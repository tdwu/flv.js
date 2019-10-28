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


class H264Demuxer {

    constructor(probeData, config) {
        this.TAG = 'H264Demuxer';

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
        return {
            match: true,
            consumed: 0,
            dataOffset: 0,
            hasAudioTrack: false,
            hasVideoTrack: true
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

        if (this._firstParse) {  // handle PreviousTagSize0 before Tag1
            this._firstParse = false;
        }
        this._parseVideoData(chunk);

        // 处理完后，通知外部（mp4复合器），可以处理数据了
        if (this._isInitialMetadataDispatched()) {
            if (this._dispatch && (this._audioTrack.length || this._videoTrack.length)) {
                this._onDataAvailable(this._audioTrack, this._videoTrack);
            }
        }

        return chunk.byteLength;
    }

    _parseVideoData(arrayBuffer) {
        let le = this._littleEndian;

        let v = new DataView(arrayBuffer, 0);
        let offset = 0;
        // 获取tagType音频为0x08；  视频为0x09； 脚本数据为0x12。
        let timestamp = v.getUint32(offset, !le);
        offset += 4;

        let naluHeader = v.getUint8(offset);
        offset += 1;
        let naluType = naluHeader & 0x1f;

        let track = this._videoTrack;
        if (naluType == 7) {
            //sps
            this._parseAVCSPSVideoData(arrayBuffer,offset);
        } else if (naluType == 8) {
            //pps

        } else if (naluType == 5) {
            // I

        } else {

        }


        this._parseAVCVideoPacket(arrayBuffer, dataOffset + 1, dataSize - 1, tagTimestamp, tagPosition, frameType);
    }

    _parseAVCSPSVideoData(arrayBuffer, offset) {
        let sps = new Uint8Array(arrayBuffer, offset, arrayBuffer.byteLength - offset);

        let track = this._videoTrack;
        let meta = this._videoMetadata;
        if (!meta) {
            this._hasVideo = true;
            this._mediaInfo.hasVideo = true;
            // 如果不存在，则先创建
            meta = this._videoMetadata = {};
            meta.type = 'video';
            meta.id = track.id;
            meta.timescale = this._timescale;
            meta.duration = this._duration;
        }


        let config = SPSParser.parseSPS(sps);
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

        mi.mimeType = 'video/x-flv; codecs="' + mi.videoCodec + '"';
        this._onMediaInfo(mi);


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
                dts: dts, // flv中的tag时间
                cts: cts, // 相对时间
                pts: (dts + cts)// 最终的player时间
            };
            // console.log(dts + ' ' + cts + ' ' + (dts + cts));
            // console.log(avcSample);
            if (keyframe) {
                avcSample.fileposition = tagPosition;
            }
            track.samples.push(avcSample);
            track.length += length;
            //console.log(track.length);

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

export default H264Demuxer;