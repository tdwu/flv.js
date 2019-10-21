/*
 * Copyright (C) 2016 Bilibili. All Rights Reserved.
 *
 * @author zheng qian <xqq@xqq.im>
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

import Log from '../utils/logger.js';
import AMF from './amf-parser.js';
import SPSParser from './sps-parser.js';
import DemuxErrors from './demux-errors.js';
import MediaInfo from '../core/media-info.js';
import {IllegalStateException} from '../utils/exception.js';

function Swap16(src) {
    return (((src >>> 8) & 0xFF) |
        ((src & 0xFF) << 8));
}

function Swap32(src) {
    return (((src & 0xFF000000) >>> 24) |
        ((src & 0x00FF0000) >>> 8) |
        ((src & 0x0000FF00) << 8) |
        ((src & 0x000000FF) << 24));
}

function ReadBig32(array, index) {
    return ((array[index] << 24) |
        (array[index + 1] << 16) |
        (array[index + 2] << 8) |
        (array[index + 3]));
}


class FLVDemuxer {

    constructor(probeData, config) {
        this.TAG = 'FLVDemuxer';

        this._config = config;

        this._onError = null;
        this._onMediaInfo = null;
        this._onMetaDataArrived = null;
        this._onScriptDataArrived = null;
        this._onTrackMetadata = null;
        this._onDataAvailable = null;

        this._dataOffset = probeData.dataOffset;
        this._firstParse = true;
        this._dispatch = false;

        this._hasAudio = probeData.hasAudioTrack;
        this._hasVideo = probeData.hasVideoTrack;

        this._hasAudioFlagOverrided = false;
        this._hasVideoFlagOverrided = false;

        this._audioInitialMetadataDispatched = false;
        this._videoInitialMetadataDispatched = false;

        // 媒体信息
        this._mediaInfo = new MediaInfo();
        this._mediaInfo.hasAudio = this._hasAudio;
        this._mediaInfo.hasVideo = this._hasVideo;
        this._metadata = null;// 由flv的script填充
        this._audioMetadata = null;// 音频元数据
        this._videoMetadata = null;// 视频元数据

        this._naluLengthSize = 4;
        this._timestampBase = 0;  // int32, in milliseconds
        this._timescale = 1000;
        this._duration = 0;  // int32, in milliseconds
        this._durationOverrided = false;
        this._referenceFrameRate = {
            fixed: true,
            fps: 23.976,
            fps_num: 23976,
            fps_den: 1000
        };

        this._flvSoundRateTable = [5500, 11025, 22050, 44100, 48000];

        this._mpegSamplingRates = [
            96000, 88200, 64000, 48000, 44100, 32000,
            24000, 22050, 16000, 12000, 11025, 8000, 7350
        ];

        this._mpegAudioV10SampleRateTable = [44100, 48000, 32000, 0];
        this._mpegAudioV20SampleRateTable = [22050, 24000, 16000, 0];
        this._mpegAudioV25SampleRateTable = [11025, 12000, 8000, 0];

        this._mpegAudioL1BitRateTable = [0, 32, 64, 96, 128, 160, 192, 224, 256, 288, 320, 352, 384, 416, 448, -1];
        this._mpegAudioL2BitRateTable = [0, 32, 48, 56, 64, 80, 96, 112, 128, 160, 192, 224, 256, 320, 384, -1];
        this._mpegAudioL3BitRateTable = [0, 32, 40, 48, 56, 64, 80, 96, 112, 128, 160, 192, 224, 256, 320, -1];

        // 视频（h264）数据处理后，就存放在这个地方
        this._videoTrack = {type: 'video', id: 1, sequenceNumber: 0, samples: [], length: 0};
        this._audioTrack = {type: 'audio', id: 2, sequenceNumber: 0, samples: [], length: 0};

        // 判断浏览器，或者系统。这个时大段还是小端（可能系统不一样或者浏览器不一样，采用大端小端不一致）
        this._littleEndian = (function () {
            let buf = new ArrayBuffer(2);
            (new DataView(buf)).setInt16(0, 256, true);  // little-endian write
            return (new Int16Array(buf))[0] === 256;  // platform-spec read, if equal then LE
        })();
    }

    destroy() {
        this._mediaInfo = null;
        this._metadata = null;
        this._audioMetadata = null;
        this._videoMetadata = null;
        this._videoTrack = null;
        this._audioTrack = null;

        this._onError = null;
        this._onMediaInfo = null;
        this._onMetaDataArrived = null;
        this._onScriptDataArrived = null;
        this._onTrackMetadata = null;
        this._onDataAvailable = null;
    }

    static probe(buffer) {
        let data = new Uint8Array(buffer);
        let mismatch = {match: false};
        if (data.length < 9) {
            console.log('flv header 长度不够');
            // 不是flv+1版本，则不匹配
            return mismatch;
        }

        // Signature(3 Byte)+Version(1 Byte)+Flags(1 Bypte)+DataOffset(4 Byte)
        // F(8) | L(8) | V(8) | Version(8) | TypeFlagsReserved(5) | TypeFlagsAudio(1)| TypeFlagsReserved(1) | TypeFlagsVideo(1) | DataOffset(32)
        if (data[0] !== 0x46 || data[1] !== 0x4C || data[2] !== 0x56 || data[3] !== 0x01) {
            console.log('flv 头部格式不匹配');
            // 不是flv+1版本，则不匹配
            return mismatch;
        }

        // flags中提取信息
        let hasAudio = ((data[4] & 4) >>> 2) !== 0;// 是否包含audio
        let hasVideo = (data[4] & 1) !== 0;// 是否包含video

        // offset 计算
        let offset = ReadBig32(data, 5);

        if (offset < 9) {
            // DataOffset为FLV Header的长度，为固定值0x00000009。
            console.log('FLV DataOffset 不对');
            return mismatch;
        }

        return {
            match: true,
            consumed: offset,
            dataOffset: offset,
            hasAudioTrack: hasAudio,
            hasVideoTrack: hasVideo
        };
    }

    bindDataSource(loader) {
        loader.onDataArrival = this.parseChunks.bind(this);
        return this;
    }

    // prototype: function(type: string, metadata: any): void
    get onTrackMetadata() {
        return this._onTrackMetadata;
    }

    set onTrackMetadata(callback) {
        this._onTrackMetadata = callback;
    }

    // prototype: function(mediaInfo: MediaInfo): void
    get onMediaInfo() {
        return this._onMediaInfo;
    }

    set onMediaInfo(callback) {
        this._onMediaInfo = callback;
    }

    get onMetaDataArrived() {
        return this._onMetaDataArrived;
    }

    set onMetaDataArrived(callback) {
        this._onMetaDataArrived = callback;
    }

    get onScriptDataArrived() {
        return this._onScriptDataArrived;
    }

    set onScriptDataArrived(callback) {
        this._onScriptDataArrived = callback;
    }

    // prototype: function(type: number, info: string): void
    get onError() {
        return this._onError;
    }

    set onError(callback) {
        this._onError = callback;
    }

    // prototype: function(videoTrack: any, audioTrack: any): void
    get onDataAvailable() {
        return this._onDataAvailable;
    }

    set onDataAvailable(callback) {
        this._onDataAvailable = callback;
    }

    // timestamp base for output samples, must be in milliseconds
    get timestampBase() {
        return this._timestampBase;
    }

    set timestampBase(base) {
        console.log('设置_timestampBase：' + base);
        this._timestampBase = base;
    }

    get overridedDuration() {
        return this._duration;
    }

    // Force-override media duration. Must be in milliseconds, int32
    set overridedDuration(duration) {
        this._durationOverrided = true;
        this._duration = duration;
        this._mediaInfo.duration = duration;
    }

    // Force-override audio track present flag, boolean
    set overridedHasAudio(hasAudio) {
        this._hasAudioFlagOverrided = true;
        this._hasAudio = hasAudio;
        this._mediaInfo.hasAudio = hasAudio;
    }

    // Force-override video track present flag, boolean
    set overridedHasVideo(hasVideo) {
        this._hasVideoFlagOverrided = true;
        this._hasVideo = hasVideo;
        this._mediaInfo.hasVideo = hasVideo;
    }

    resetMediaInfo() {
        this._mediaInfo = new MediaInfo();
    }

    _isInitialMetadataDispatched() {
        if (this._hasAudio && this._hasVideo) {  // both audio & video
            return this._audioInitialMetadataDispatched && this._videoInitialMetadataDispatched;
        }
        if (this._hasAudio && !this._hasVideo) {  // audio only
            return this._audioInitialMetadataDispatched;
        }
        if (!this._hasAudio && this._hasVideo) {  // video only
            return this._videoInitialMetadataDispatched;
        }
        return false;
    }

    // 收到数据
    // function parseChunks(chunk: ArrayBuffer, byteStart: number): number;
    parseChunks(chunk, byteStart) {
        // 对应IOController中的_dispatchChunks
        if (!this._onError || !this._onMediaInfo || !this._onTrackMetadata || !this._onDataAvailable) {
            throw new IllegalStateException('Flv: onError & onMediaInfo & onTrackMetadata & onDataAvailable callback must be specified');
        }

        let offset = 0;
        let le = this._littleEndian;

        if (byteStart === 0) {  // buffer with FLV header
            // 第一次来，则是flv的header开头
            if (chunk.byteLength > 13) {
                let probeData = FLVDemuxer.probe(chunk);
                offset = probeData.dataOffset;
            } else {
                return 0;
            }
        }

        if (this._firstParse) {  // handle PreviousTagSize0 before Tag1
            this._firstParse = false;
            if (byteStart + offset !== this._dataOffset) {
                Log.w(this.TAG, 'First time parsing but chunk byteStart invalid!');
            }

            // 前一个tag size
            let v = new DataView(chunk, offset);
            let prevTagSize0 = v.getUint32(0, !le);
            if (prevTagSize0 !== 0) {
                Log.w(this.TAG, 'PrevTagSize0 !== 0 !!!');
            }
            offset += 4;
        }

        while (offset < chunk.byteLength) {
            this._dispatch = true;

            let v = new DataView(chunk, offset);

            // tag header（11）+data(任何一种数据，都超过4 字节)
            if (offset + 11 + 4 > chunk.byteLength) {
                // data not enough for parsing an flv tag
                break;
            }

            // 获取tagType音频为0x08；  视频为0x09； 脚本数据为0x12。
            let tagType = v.getUint8(0);
            // 获取dataSize
            let dataSize = v.getUint32(0, !le) & 0x00FFFFFF;//3个字节，所以取出4个，只看后面3个

            if (offset + 11 + dataSize + 4 > chunk.byteLength) {
                // data not enough for parsing actual data body
                break;
            }

            if (tagType !== 8 && tagType !== 9 && tagType !== 18) {
                Log.w(this.TAG, `Unsupported tag type ${tagType}, skipped`);
                // consume the whole tag (skip it)
                offset += 11 + dataSize + 4;
                continue;
            }
            let ts2 = v.getUint8(4);
            let ts1 = v.getUint8(5);
            let ts0 = v.getUint8(6);
            let ts3 = v.getUint8(7);// TimestampExtended的字节

            // Timestamp 合并+TimestampExtended
            let timestamp = ts0 | (ts1 << 8) | (ts2 << 16) | (ts3 << 24);

            let streamId = v.getUint32(7, !le) & 0x00FFFFFF;//3个字节，所以取出4个，只看后面3个
            if (streamId !== 0) {
                Log.w(this.TAG, 'Meet tag which has StreamID != 0!');
            }

            let dataOffset = offset + 11;// tag header的总长度11

            //console.log('tag type:' + tagType + " " + offset);
            switch (tagType) {
                case 8:  // Audio
                    this._parseAudioData(chunk, dataOffset, dataSize, timestamp);
                    break;
                case 9:  // Video
                    this._parseVideoData(chunk, dataOffset, dataSize, timestamp, byteStart + offset);
                    break;
                case 18:  // ScriptDataObject
                    this._parseScriptData(chunk, dataOffset, dataSize);
                    break;
            }

            let prevTagSize = v.getUint32(11 + dataSize, !le);
            if (prevTagSize !== 11 + dataSize) {
                Log.w(this.TAG, `Invalid PrevTagSize ${prevTagSize}`);
            }

            offset += 11 + dataSize + 4;  // tagBody + dataSize + prevTagSize
        }

        // 处理完后，通知外部（mp4复合器），可以处理数据了
        // dispatch parsed frames to consumer (typically, the remuxer)
        if (this._isInitialMetadataDispatched()) {
            if (this._dispatch && (this._audioTrack.length || this._videoTrack.length)) {
                this._onDataAvailable(this._audioTrack, this._videoTrack);
            }
        }

        return offset;  // consumed bytes, just equals latest offset index
    }

    _parseScriptData(arrayBuffer, dataOffset, dataSize) {
        let scriptData = AMF.parseScriptData(arrayBuffer, dataOffset, dataSize);

        console.log('_parseScriptData');
        console.log(scriptData);
        if (scriptData.hasOwnProperty('onMetaData')) {
            if (scriptData.onMetaData == null || typeof scriptData.onMetaData !== 'object') {
                Log.w(this.TAG, 'Invalid onMetaData structure!');
                return;
            }
            if (this._metadata) {
                Log.w(this.TAG, 'Found another onMetaData tag!');
            }
            console.log(this._metadata);
            let onMetaData = this._metadata.onMetaData;

            if (this._onMetaDataArrived) {
                this._onMetaDataArrived(Object.assign({}, onMetaData));
            }

            if (typeof onMetaData.hasAudio === 'boolean') {  // hasAudio
                if (this._hasAudioFlagOverrided === false) {
                    this._hasAudio = onMetaData.hasAudio;
                    this._mediaInfo.hasAudio = this._hasAudio;
                }
            }
            if (typeof onMetaData.hasVideo === 'boolean') {  // hasVideo
                if (this._hasVideoFlagOverrided === false) {
                    this._hasVideo = onMetaData.hasVideo;
                    this._mediaInfo.hasVideo = this._hasVideo;
                }
            }
            if (typeof onMetaData.audiodatarate === 'number') {  // audiodatarate
                this._mediaInfo.audioDataRate = onMetaData.audiodatarate;
            }
            if (typeof onMetaData.videodatarate === 'number') {  // videodatarate
                this._mediaInfo.videoDataRate = onMetaData.videodatarate;
            }
            if (typeof onMetaData.width === 'number') {  // width
                this._mediaInfo.width = onMetaData.width;
            }
            if (typeof onMetaData.height === 'number') {  // height
                this._mediaInfo.height = onMetaData.height;
            }
            if (typeof onMetaData.duration === 'number') {  // duration
                if (!this._durationOverrided) {
                    let duration = Math.floor(onMetaData.duration * this._timescale);
                    this._duration = duration;
                    this._mediaInfo.duration = duration;
                }
            } else {
                this._mediaInfo.duration = 0;
            }
            if (typeof onMetaData.framerate === 'number') {  // framerate
                let fps_num = Math.floor(onMetaData.framerate * 1000);
                if (fps_num > 0) {
                    let fps = fps_num / 1000;
                    this._referenceFrameRate.fixed = true;
                    this._referenceFrameRate.fps = fps;
                    this._referenceFrameRate.fps_num = fps_num;
                    this._referenceFrameRate.fps_den = 1000;
                    this._mediaInfo.fps = fps;
                }
            }
            if (typeof onMetaData.keyframes === 'object') {  // keyframes
                this._mediaInfo.hasKeyframesIndex = true;
                let keyframes = onMetaData.keyframes;
                this._mediaInfo.keyframesIndex = this._parseKeyframesIndex(keyframes);
                onMetaData.keyframes = null;  // keyframes has been extracted, remove it
            } else {
                this._mediaInfo.hasKeyframesIndex = false;
            }
            this._dispatch = false;
            this._mediaInfo.metadata = onMetaData;
            Log.v(this.TAG, 'Parsed onMetaData');
            if (this._mediaInfo.isComplete()) {
                this._onMediaInfo(this._mediaInfo);
            }
        }

        if (Object.keys(scriptData).length > 0) {
            if (this._onScriptDataArrived) {
                this._onScriptDataArrived(Object.assign({}, scriptData));
            }
        }
    }

    _parseKeyframesIndex(keyframes) {
        let times = [];
        let filepositions = [];

        // ignore first keyframe which is actually AVC Sequence Header (AVCDecoderConfigurationRecord)
        for (let i = 1; i < keyframes.times.length; i++) {
            let time = this._timestampBase + Math.floor(keyframes.times[i] * 1000);
            times.push(time);
            filepositions.push(keyframes.filepositions[i]);
        }

        return {
            times: times,
            filepositions: filepositions
        };
    }

    _parseAudioData(arrayBuffer, dataOffset, dataSize, tagTimestamp) {
        if (dataSize <= 1) {
            Log.w(this.TAG, 'Flv: Invalid audio packet, missing SoundData payload!');
            return;
        }

        if (this._hasAudioFlagOverrided === true && this._hasAudio === false) {
            // If hasAudio: false indicated explicitly in MediaDataSource,
            // Ignore all the audio packets
            return;
        }

        let le = this._littleEndian;
        let v = new DataView(arrayBuffer, dataOffset, dataSize);

        let soundSpec = v.getUint8(0);

        let soundFormat = soundSpec >>> 4;
        if (soundFormat !== 2 && soundFormat !== 10) {  // MP3 or AAC
            this._onError(DemuxErrors.CODEC_UNSUPPORTED, 'Flv: Unsupported audio codec idx: ' + soundFormat);
            return;
        }

        let soundRate = 0;
        let soundRateIndex = (soundSpec & 12) >>> 2;
        if (soundRateIndex >= 0 && soundRateIndex <= 4) {
            soundRate = this._flvSoundRateTable[soundRateIndex];
        } else {
            this._onError(DemuxErrors.FORMAT_ERROR, 'Flv: Invalid audio sample rate idx: ' + soundRateIndex);
            return;
        }

        let soundSize = (soundSpec & 2) >>> 1;  // unused
        let soundType = (soundSpec & 1);


        let meta = this._audioMetadata;
        let track = this._audioTrack;

        if (!meta) {
            if (this._hasAudio === false && this._hasAudioFlagOverrided === false) {
                this._hasAudio = true;
                this._mediaInfo.hasAudio = true;
            }

            // initial metadata
            meta = this._audioMetadata = {};
            meta.type = 'audio';
            meta.id = track.id;
            meta.timescale = this._timescale;
            meta.duration = this._duration;
            meta.audioSampleRate = soundRate;
            meta.channelCount = (soundType === 0 ? 1 : 2);
        }

        if (soundFormat === 10) {  // AAC
            let aacData = this._parseAACAudioData(arrayBuffer, dataOffset + 1, dataSize - 1);
            if (aacData == undefined) {
                return;
            }

            if (aacData.packetType === 0) {  // AAC sequence header (AudioSpecificConfig)
                if (meta.config) {
                    Log.w(this.TAG, 'Found another AudioSpecificConfig!');
                }
                let misc = aacData.data;
                meta.audioSampleRate = misc.samplingRate;
                meta.channelCount = misc.channelCount;
                meta.codec = misc.codec;
                meta.originalCodec = misc.originalCodec;
                meta.config = misc.config;
                // The decode result of an aac sample is 1024 PCM samples
                meta.refSampleDuration = 1024 / meta.audioSampleRate * meta.timescale;
                Log.v(this.TAG, 'Parsed AudioSpecificConfig');

                if (this._isInitialMetadataDispatched()) {
                    // Non-initial metadata, force dispatch (or flush) parsed frames to remuxer
                    if (this._dispatch && (this._audioTrack.length || this._videoTrack.length)) {
                        this._onDataAvailable(this._audioTrack, this._videoTrack);
                    }
                } else {
                    this._audioInitialMetadataDispatched = true;
                }
                // then notify new metadata
                this._dispatch = false;
                this._onTrackMetadata('audio', meta);

                let mi = this._mediaInfo;
                mi.audioCodec = meta.originalCodec;
                mi.audioSampleRate = meta.audioSampleRate;
                mi.audioChannelCount = meta.channelCount;
                if (mi.hasVideo) {
                    if (mi.videoCodec != null) {
                        mi.mimeType = 'video/x-flv; codecs="' + mi.videoCodec + ',' + mi.audioCodec + '"';
                    }
                } else {
                    mi.mimeType = 'video/x-flv; codecs="' + mi.audioCodec + '"';
                }
                if (mi.isComplete()) {
                    this._onMediaInfo(mi);
                }
            } else if (aacData.packetType === 1) {  // AAC raw frame data
                let dts = this._timestampBase + tagTimestamp;
                let aacSample = {unit: aacData.data, length: aacData.data.byteLength, dts: dts, pts: dts};
                track.samples.push(aacSample);
                track.length += aacData.data.length;
            } else {
                Log.e(this.TAG, `Flv: Unsupported AAC data type ${aacData.packetType}`);
            }
        } else if (soundFormat === 2) {  // MP3
            if (!meta.codec) {
                // We need metadata for mp3 audio track, extract info from frame header
                let misc = this._parseMP3AudioData(arrayBuffer, dataOffset + 1, dataSize - 1, true);
                if (misc == undefined) {
                    return;
                }
                meta.audioSampleRate = misc.samplingRate;
                meta.channelCount = misc.channelCount;
                meta.codec = misc.codec;
                meta.originalCodec = misc.originalCodec;
                // The decode result of an mp3 sample is 1152 PCM samples
                meta.refSampleDuration = 1152 / meta.audioSampleRate * meta.timescale;
                Log.v(this.TAG, 'Parsed MPEG Audio Frame Header');

                this._audioInitialMetadataDispatched = true;
                this._onTrackMetadata('audio', meta);

                let mi = this._mediaInfo;
                mi.audioCodec = meta.codec;
                mi.audioSampleRate = meta.audioSampleRate;
                mi.audioChannelCount = meta.channelCount;
                mi.audioDataRate = misc.bitRate;
                if (mi.hasVideo) {
                    if (mi.videoCodec != null) {
                        mi.mimeType = 'video/x-flv; codecs="' + mi.videoCodec + ',' + mi.audioCodec + '"';
                    }
                } else {
                    mi.mimeType = 'video/x-flv; codecs="' + mi.audioCodec + '"';
                }
                if (mi.isComplete()) {
                    this._onMediaInfo(mi);
                }
            }

            // This packet is always a valid audio packet, extract it
            let data = this._parseMP3AudioData(arrayBuffer, dataOffset + 1, dataSize - 1, false);
            if (data == undefined) {
                return;
            }
            let dts = this._timestampBase + tagTimestamp;
            let mp3Sample = {unit: data, length: data.byteLength, dts: dts, pts: dts};
            track.samples.push(mp3Sample);
            track.length += data.length;
        }
    }

    _parseAACAudioData(arrayBuffer, dataOffset, dataSize) {
        if (dataSize <= 1) {
            Log.w(this.TAG, 'Flv: Invalid AAC packet, missing AACPacketType or/and Data!');
            return;
        }

        let result = {};
        let array = new Uint8Array(arrayBuffer, dataOffset, dataSize);

        result.packetType = array[0];

        if (array[0] === 0) {
            result.data = this._parseAACAudioSpecificConfig(arrayBuffer, dataOffset + 1, dataSize - 1);
        } else {
            result.data = array.subarray(1);
        }

        return result;
    }

    _parseAACAudioSpecificConfig(arrayBuffer, dataOffset, dataSize) {
        let array = new Uint8Array(arrayBuffer, dataOffset, dataSize);
        let config = null;

        /* Audio Object Type:
           0: Null
           1: AAC Main
           2: AAC LC
           3: AAC SSR (Scalable Sample Rate)
           4: AAC LTP (Long Term Prediction)
           5: HE-AAC / SBR (Spectral Band Replication)
           6: AAC Scalable
        */

        let audioObjectType = 0;
        let originalAudioObjectType = 0;
        let audioExtensionObjectType = null;
        let samplingIndex = 0;
        let extensionSamplingIndex = null;

        // 5 bits
        audioObjectType = originalAudioObjectType = array[0] >>> 3;
        // 4 bits
        samplingIndex = ((array[0] & 0x07) << 1) | (array[1] >>> 7);
        if (samplingIndex < 0 || samplingIndex >= this._mpegSamplingRates.length) {
            this._onError(DemuxErrors.FORMAT_ERROR, 'Flv: AAC invalid sampling frequency index!');
            return;
        }

        let samplingFrequence = this._mpegSamplingRates[samplingIndex];

        // 4 bits
        let channelConfig = (array[1] & 0x78) >>> 3;
        if (channelConfig < 0 || channelConfig >= 8) {
            this._onError(DemuxErrors.FORMAT_ERROR, 'Flv: AAC invalid channel configuration');
            return;
        }

        if (audioObjectType === 5) {  // HE-AAC?
            // 4 bits
            extensionSamplingIndex = ((array[1] & 0x07) << 1) | (array[2] >>> 7);
            // 5 bits
            audioExtensionObjectType = (array[2] & 0x7C) >>> 2;
        }

        // workarounds for various browsers
        let userAgent = self.navigator.userAgent.toLowerCase();

        if (userAgent.indexOf('firefox') !== -1) {
            // firefox: use SBR (HE-AAC) if freq less than 24kHz
            if (samplingIndex >= 6) {
                audioObjectType = 5;
                config = new Array(4);
                extensionSamplingIndex = samplingIndex - 3;
            } else {  // use LC-AAC
                audioObjectType = 2;
                config = new Array(2);
                extensionSamplingIndex = samplingIndex;
            }
        } else if (userAgent.indexOf('android') !== -1) {
            // android: always use LC-AAC
            audioObjectType = 2;
            config = new Array(2);
            extensionSamplingIndex = samplingIndex;
        } else {
            // for other browsers, e.g. chrome...
            // Always use HE-AAC to make it easier to switch aac codec profile
            audioObjectType = 5;
            extensionSamplingIndex = samplingIndex;
            config = new Array(4);

            if (samplingIndex >= 6) {
                extensionSamplingIndex = samplingIndex - 3;
            } else if (channelConfig === 1) {  // Mono channel
                audioObjectType = 2;
                config = new Array(2);
                extensionSamplingIndex = samplingIndex;
            }
        }

        config[0] = audioObjectType << 3;
        config[0] |= (samplingIndex & 0x0F) >>> 1;
        config[1] = (samplingIndex & 0x0F) << 7;
        config[1] |= (channelConfig & 0x0F) << 3;
        if (audioObjectType === 5) {
            config[1] |= ((extensionSamplingIndex & 0x0F) >>> 1);
            config[2] = (extensionSamplingIndex & 0x01) << 7;
            // extended audio object type: force to 2 (LC-AAC)
            config[2] |= (2 << 2);
            config[3] = 0;
        }

        return {
            config: config,
            samplingRate: samplingFrequence,
            channelCount: channelConfig,
            codec: 'mp4a.40.' + audioObjectType,
            originalCodec: 'mp4a.40.' + originalAudioObjectType
        };
    }

    _parseMP3AudioData(arrayBuffer, dataOffset, dataSize, requestHeader) {
        if (dataSize < 4) {
            Log.w(this.TAG, 'Flv: Invalid MP3 packet, header missing!');
            return;
        }

        let le = this._littleEndian;
        let array = new Uint8Array(arrayBuffer, dataOffset, dataSize);
        let result = null;

        if (requestHeader) {
            if (array[0] !== 0xFF) {
                return;
            }
            let ver = (array[1] >>> 3) & 0x03;
            let layer = (array[1] & 0x06) >> 1;

            let bitrate_index = (array[2] & 0xF0) >>> 4;
            let sampling_freq_index = (array[2] & 0x0C) >>> 2;

            let channel_mode = (array[3] >>> 6) & 0x03;
            let channel_count = channel_mode !== 3 ? 2 : 1;

            let sample_rate = 0;
            let bit_rate = 0;
            let object_type = 34;  // Layer-3, listed in MPEG-4 Audio Object Types

            let codec = 'mp3';

            switch (ver) {
                case 0:  // MPEG 2.5
                    sample_rate = this._mpegAudioV25SampleRateTable[sampling_freq_index];
                    break;
                case 2:  // MPEG 2
                    sample_rate = this._mpegAudioV20SampleRateTable[sampling_freq_index];
                    break;
                case 3:  // MPEG 1
                    sample_rate = this._mpegAudioV10SampleRateTable[sampling_freq_index];
                    break;
            }

            switch (layer) {
                case 1:  // Layer 3
                    object_type = 34;
                    if (bitrate_index < this._mpegAudioL3BitRateTable.length) {
                        bit_rate = this._mpegAudioL3BitRateTable[bitrate_index];
                    }
                    break;
                case 2:  // Layer 2
                    object_type = 33;
                    if (bitrate_index < this._mpegAudioL2BitRateTable.length) {
                        bit_rate = this._mpegAudioL2BitRateTable[bitrate_index];
                    }
                    break;
                case 3:  // Layer 1
                    object_type = 32;
                    if (bitrate_index < this._mpegAudioL1BitRateTable.length) {
                        bit_rate = this._mpegAudioL1BitRateTable[bitrate_index];
                    }
                    break;
            }

            result = {
                bitRate: bit_rate,
                samplingRate: sample_rate,
                channelCount: channel_count,
                codec: codec,
                originalCodec: codec
            };
        } else {
            result = array;
        }

        return result;
    }

    _parseVideoData(arrayBuffer, dataOffset, dataSize, tagTimestamp, tagPosition) {
        if (dataSize <= 1) {
            Log.w(this.TAG, 'Flv: Invalid video packet, missing VideoData payload!');
            return;
        }

        if (this._hasVideoFlagOverrided === true && this._hasVideo === false) {
            // If hasVideo: false indicated explicitly in MediaDataSource,
            // Ignore all the video packets
            return;
        }

        let spec = (new Uint8Array(arrayBuffer, dataOffset, dataSize))[0];

        //Video Header = | FrameType(4) | CodecID(4) |
        let frameType = (spec & 240) >>> 4;//数据类型，1为关键帧，2为非关键帧，3为h263的非关键帧，4为服务器生成关键帧，5为视频信息或命令帧。
        let codecId = spec & 15;// 包装类型，1为JPEG，2为H263，3为Screen video，4为On2 VP6，5为On2 VP6，6为Screen videoversion 2，7为AVC。

        // 只支持h264
        if (codecId !== 7) {
            this._onError(DemuxErrors.CODEC_UNSUPPORTED, `Flv: Unsupported codec in video frame: ${codecId}`);
            return;
        }

        /*
          VideoData为数据具体内容：
          如果CodecID=2，为H263VideoPacket；
          如果CodecID=3，为ScreenVideopacket；
          如果CodecID=4，为VP6FLVVideoPacket；
          如果CodecID=5，为VP6FLVAlphaVideoPacket；
          如果CodecID=6，为ScreenV2VideoPacket；
          如果CodecID=7，为AVCVideoPacket；(H.264/MPEG-4 AVC)，vp8 抗衡

          codecid=12,h265(hevc)(国内私有)，vp9 抗衡
          */

        this._parseAVCVideoPacket(arrayBuffer, dataOffset + 1, dataSize - 1, tagTimestamp, tagPosition, frameType);
    }

    /***
     *  AVCVideoPacket格式

     AVCVideoPacket同样包括Packet Header和Packet Body两部分：

     即AVCVideoPacket Format：

     | AVCPacketType(8)| CompostionTime(24) | Data |

     AVCPacketType为包的类型：

     如果AVCPacketType=0x00，为AVCSequence Header；

     如果AVCPacketType=0x01，为AVC NALU；

     如果AVCPacketType=0x02，为AVC end ofsequence

     CompositionTime为相对时间戳：

     如果AVCPacketType=0x01， 为相对时间戳；

     其它，均为0；

     Data为负载数据：

     如果AVCPacketType=0x00，为AVCDecorderConfigurationRecord；

     如果AVCPacketType=0x01，为NALUs；

     如果AVCPacketType=0x02，为空。
     * @param arrayBuffer
     * @param dataOffset
     * @param dataSize
     * @param tagTimestamp
     * @param tagPosition
     * @param frameType
     * @private
     */
    _parseAVCVideoPacket(arrayBuffer, dataOffset, dataSize, tagTimestamp, tagPosition, frameType) {
        if (dataSize < 4) {
            Log.w(this.TAG, 'Flv: Invalid AVC packet, missing AVCPacketType or/and CompositionTime');
            return;
        }

        let le = this._littleEndian;
        let v = new DataView(arrayBuffer, dataOffset, dataSize);

        // 获取AVCPacketType
        let packetType = v.getUint8(0);
        //获取CompostionTime（相对时间戳），只取3位
        let cts_unsigned = v.getUint32(0, !le) & 0x00FFFFFF;
        let cts = (cts_unsigned << 8) >> 8;  // convert to 24-bit signed int

        if (packetType === 0) {
            // AVCDecoderConfigurationRecord
            // 配置等信息
            this._parseAVCDecoderConfigurationRecord(arrayBuffer, dataOffset + 4, dataSize - 4);
        } else if (packetType === 1) {
            // One or more Nalus
            this._parseAVCVideoData(arrayBuffer, dataOffset + 4, dataSize - 4, tagTimestamp, tagPosition, frameType, cts);
        } else if (packetType === 2) {
            // empty, AVC end of sequence
        } else {
            this._onError(DemuxErrors.FORMAT_ERROR, `Flv: Invalid video packet type ${packetType}`);
            return;
        }
    }

    _parseAVCDecoderConfigurationRecord(arrayBuffer, dataOffset, dataSize) {
        if (dataSize < 7) {
            Log.w(this.TAG, 'Flv: Invalid AVCDecoderConfigurationRecord, lack of data!');
            return;
        }


        console.log('AVCDecoderConfigurationRecord');
        // 视频元数据
        let meta = this._videoMetadata;
        let track = this._videoTrack;
        let le = this._littleEndian;
        let v = new DataView(arrayBuffer, dataOffset, dataSize);

        if (!meta) {
            if (this._hasVideo === false && this._hasVideoFlagOverrided === false) {
                this._hasVideo = true;
                this._mediaInfo.hasVideo = true;
            }

            // 如果不存在，则先创建
            meta = this._videoMetadata = {};
            meta.type = 'video';
            meta.id = track.id;
            meta.timescale = this._timescale;
            meta.duration = this._duration;
        } else {
            if (typeof meta.avcc !== 'undefined') {
                Log.w(this.TAG, 'Found another AVCDecoderConfigurationRecord!');
            }
        }

        // 格式如下：
        //| cfgVersion(8) | avcProfile(8) | profileCompatibility(8) |avcLevel(8) | reserved(6) | lengthSizeMinusOne(2) | reserved(3) | numOfSPS(5) |spsLength(16) | sps(n) | numOfPPS(8) | ppsLength(16) | pps(n) |
        let version = v.getUint8(0);  // configurationVersion
        let avcProfile = v.getUint8(1);  // avcProfileIndication
        let profileCompatibility = v.getUint8(2);  // profile_compatibility
        let avcLevel = v.getUint8(3);  // AVCLevelIndication

        if (version !== 1 || avcProfile === 0) {
            this._onError(DemuxErrors.FORMAT_ERROR, 'Flv: Invalid AVCDecoderConfigurationRecord');
            return;
        }

        // nalu header size？
        this._naluLengthSize = (v.getUint8(4) & 3) + 1;  // lengthSizeMinusOne
        if (this._naluLengthSize !== 3 && this._naluLengthSize !== 4) {  // holy shit!!!
            this._onError(DemuxErrors.FORMAT_ERROR, `Flv: Strange NaluLengthSizeMinusOne: ${this._naluLengthSize - 1}`);
            return;
        }

        //【1】 sps处理
        let spsCount = v.getUint8(5) & 31;  // numOfSequenceParameterSets
        if (spsCount === 0) {
            this._onError(DemuxErrors.FORMAT_ERROR, 'Flv: Invalid AVCDecoderConfigurationRecord: No SPS');
            return;
        } else if (spsCount > 1) {
            Log.w(this.TAG, `Flv: Strange AVCDecoderConfigurationRecord: SPS Count = ${spsCount}`);
        }

        let offset = 6;

        // 从sps中提取信息
        for (let i = 0; i < spsCount; i++) {
            let len = v.getUint16(offset, !le);  // sequenceParameterSetLength
            offset += 2;

            if (len === 0) {
                continue;
            }

            // Notice: Nalu without startcode header (00 00 00 01)
            let sps = new Uint8Array(arrayBuffer, dataOffset + offset, len);
            offset += len;

            // 提取出sps信息
            let config = SPSParser.parseSPS(sps);
            if (i !== 0) {
                // ignore other sps's config
                continue;
            }

            meta.codecWidth = config.codec_size.width;
            meta.codecHeight = config.codec_size.height;
            meta.presentWidth = config.present_size.width;
            meta.presentHeight = config.present_size.height;

            meta.profile = config.profile_string;
            meta.level = config.level_string;
            meta.bitDepth = config.bit_depth;
            meta.chromaFormat = config.chroma_format;
            meta.sarRatio = config.sar_ratio;
            meta.frameRate = config.frame_rate;

            if (config.frame_rate.fixed === false ||
                config.frame_rate.fps_num === 0 ||
                config.frame_rate.fps_den === 0) {
                meta.frameRate = this._referenceFrameRate;
            }

            let fps_den = meta.frameRate.fps_den;
            let fps_num = meta.frameRate.fps_num;
            meta.refSampleDuration = meta.timescale * (fps_den / fps_num);

            let codecArray = sps.subarray(1, 4);
            let codecString = 'avc1.';
            for (let j = 0; j < 3; j++) {
                let h = codecArray[j].toString(16);
                if (h.length < 2) {
                    h = '0' + h;
                }
                codecString += h;
            }
            meta.codec = codecString;

            // 媒体信息
            let mi = this._mediaInfo;
            mi.width = meta.codecWidth;
            mi.height = meta.codecHeight;
            mi.fps = meta.frameRate.fps;
            mi.profile = meta.profile;
            mi.level = meta.level;
            mi.refFrames = config.ref_frames;
            mi.chromaFormat = config.chroma_format_string;
            mi.sarNum = meta.sarRatio.width;
            mi.sarDen = meta.sarRatio.height;
            mi.videoCodec = codecString;

            console.log('mediaInfo');
            console.log(mi);
            console.log('videoMediaData');
            console.log(meta);
            if (mi.hasAudio) {
                if (mi.audioCodec != null) {
                    mi.mimeType = 'video/x-flv; codecs="' + mi.videoCodec + ',' + mi.audioCodec + '"';
                }
            } else {
                mi.mimeType = 'video/x-flv; codecs="' + mi.videoCodec + '"';
            }
            if (mi.isComplete()) {
                console.log('mediaInfo 加载完成');
                this._onMediaInfo(mi);
            }
        }


        //【1】 pps处理
        let ppsCount = v.getUint8(offset);  // numOfPictureParameterSets
        if (ppsCount === 0) {
            this._onError(DemuxErrors.FORMAT_ERROR, 'Flv: Invalid AVCDecoderConfigurationRecord: No PPS');
            return;
        } else if (ppsCount > 1) {
            Log.w(this.TAG, `Flv: Strange AVCDecoderConfigurationRecord: PPS Count = ${ppsCount}`);
        }

        offset++;

        for (let i = 0; i < ppsCount; i++) {
            let len = v.getUint16(offset, !le);  // pictureParameterSetLength
            offset += 2;

            if (len === 0) {
                continue;
            }

            // pps is useless for extracting video information
            offset += len;
        }

        meta.avcc = new Uint8Array(dataSize);
        meta.avcc.set(new Uint8Array(arrayBuffer, dataOffset, dataSize), 0);
        Log.v(this.TAG, 'Parsed AVCDecoderConfigurationRecord');

        if (this._isInitialMetadataDispatched()) {
            // flush parsed frames
            if (this._dispatch && (this._audioTrack.length || this._videoTrack.length)) {
                this._onDataAvailable(this._audioTrack, this._videoTrack);
            }
        } else {
            this._videoInitialMetadataDispatched = true;
        }
        // notify new metadata
        this._dispatch = false;
        this._onTrackMetadata('video', meta);
    }

    _parseAVCVideoData(arrayBuffer, dataOffset, dataSize, tagTimestamp, tagPosition, frameType, cts) {
        let le = this._littleEndian;
        let v = new DataView(arrayBuffer, dataOffset, dataSize);

        let units = [], length = 0;

        let offset = 0;
        // 协议中nalv 长度，用几个直接存储传输
        const lengthSize = this._naluLengthSize;
        //cts 相对时间
        //tagTimestamp flv tag 中的时间
        let dts = this._timestampBase + tagTimestamp;
        let keyframe = (frameType === 1);  // from FLV Frame Type constants

        while (offset < dataSize) {
            if (offset + 4 >= dataSize) {
                Log.w(this.TAG, `Malformed Nalu near timestamp ${dts}, offset = ${offset}, dataSize = ${dataSize}`);
                break;  // data not enough for next Nalu
            }
            // Nalu with length-header (AVC1)
            let naluSize = v.getUint32(offset, !le);  // Big-Endian read
            // console.log('naluSize:'+ naluSize);
            if (lengthSize === 3) {
                // 如果是3个字节。只取3个直接
                naluSize >>>= 8;
            }
            if (naluSize > dataSize - lengthSize) {
                Log.w(this.TAG, `Malformed Nalus near timestamp ${dts}, NaluSize > DataSize!`);
                return;
            }

            let unitType = v.getUint8(offset + lengthSize) & 0x1F;

            if (unitType === 5) {  // IDR
                keyframe = true;
            }

            // 一帧数据，存入units中去(缓冲区，等待mp4符合器取出进行合并)
            let data = new Uint8Array(arrayBuffer, dataOffset + offset, lengthSize + naluSize);
            // let unit = {type: unitType, data: data};
            units.push({type: unitType, data: data});
            length += data.byteLength;

            offset += lengthSize + naluSize;
        }

        if (units.length) {
            let track = this._videoTrack;
            let avcSample = {
                units: units,
                length: length,
                isKeyframe: keyframe,
                dts: dts,// flv中的tag时间
                cts: cts,// 相对时间
                pts: (dts + cts)// 最终的player时间
            };
            // console.log(dts + ' ' + cts + ' ' + (dts + cts));
            // console.log(avcSample);
            if (keyframe) {
                avcSample.fileposition = tagPosition;
            }
            track.samples.push(avcSample);
            track.length += length;

            /**
             *
             *
             * DTS和PTS的不同：

             * DTS主要用于视频的解码,在解码阶段使用.

             * PTS主要用于视频的同步和输出.在display的时候使用.

             * 在没有B frame的情况下.DTS和PTS的输出顺序是一样的.（这点很重要）

             * compositionTime = (PTS - DTS) / 90.0
             *
             * **/
        }
    }

}

export default FLVDemuxer;