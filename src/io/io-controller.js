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
import SpeedSampler from './speed-sampler.js';
import {LoaderErrors} from './loader.js';
import FetchStreamLoader from './fetch-stream-loader.js';
import MozChunkedLoader from './xhr-moz-chunked-loader.js';
import RangeLoader from './xhr-range-loader.js';
import WebSocketLoader from './websocket-loader.js';
import RangeSeekHandler from './range-seek-handler.js';
import ParamSeekHandler from './param-seek-handler.js';
import {IllegalStateException, InvalidArgumentException, RuntimeException} from '../utils/exception.js';

/**
 * DataSource: {
 *     url: string,
 *     filesize: number,
 *     cors: boolean,
 *     withCredentials: boolean
 * }
 *
 */

// Manage IO Loaders
class IOController {

    constructor(dataSource, config, extraData) {
        this.TAG = 'IOController';

        this._config = config;
        this._extraData = extraData;

        // 暂存区/缓存区大小，可由外部config 中设置
        this._stashInitialSize = 1024 * 384;  // default initial size: 384KB
        if (config.stashInitialSize != undefined && config.stashInitialSize > 0) {
            // apply from config
            this._stashInitialSize = config.stashInitialSize;
        }

        this._stashUsed = 0;// 已使用空间，
        this._stashSize = this._stashInitialSize;//  真实大小
        this._bufferSize = 1024 * 1024 * 3;  // initial size: 3MB// 缓冲区大小
        this._stashBuffer = new ArrayBuffer(this._bufferSize);//暂存区的缓冲大小
        this._stashByteStart = 0;
        this._enableStash = true; //是否开启暂存
        if (config.enableStashBuffer === false) {
            this._enableStash = false;
        }
        this.lastByteStart = -1;

        this._loader = null;//真正的loader
        this._loaderClass = null;
        this._seekHandler = null;

        this._dataSource = dataSource;
        this._isWebSocketURL = /wss?:\/\/(.+?)/.test(dataSource.url);
        this._refTotalLength = dataSource.filesize ? dataSource.filesize : null;
        this._totalLength = this._refTotalLength;
        this._fullRequestFlag = false;
        this._currentRange = null;
        this._redirectedURL = null;

        this._speedNormalized = 0;// 所属范围的常规速率
        this._speedSampler = new SpeedSampler();//下载速度采样记录器
        // 常规速率定义，暂存区的大小旧时根据这个来调节
        this._speedNormalizeList = [64, 128, 256, 384, 512, 768, 1024, 1536, 2048, 3072, 4096];

        this._isEarlyEofReconnecting = false;

        this._paused = false;
        this._resumeFrom = 0;

        // 暴露出去的事件
        this._onDataArrival = null;
        this._onSeeked = null;
        this._onError = null;
        this._onComplete = null;
        this._onRedirect = null;
        this._onRecoveredEarlyEof = null;

        // 快进处理handler， 没看懂怎么使用
        this._selectSeekHandler();
        //选择io加载器，确定_loaderClass，进行网络下载
        this._selectLoader();
        // 根据_loaderClass进行实例化，并绑定事件监听
        this._createLoader();
    }

    destroy() {
        if (this._loader.isWorking()) {
            this._loader.abort();
        }
        this._loader.destroy();
        this._loader = null;
        this._loaderClass = null;
        this._dataSource = null;
        this._stashBuffer = null;
        this._stashUsed = this._stashSize = this._bufferSize = this._stashByteStart = 0;
        this._currentRange = null;
        this._speedSampler = null;

        this._isEarlyEofReconnecting = false;

        this._onDataArrival = null;
        this._onSeeked = null;
        this._onError = null;
        this._onComplete = null;
        this._onRedirect = null;
        this._onRecoveredEarlyEof = null;

        this._extraData = null;
    }

    isWorking() {
        return this._loader && this._loader.isWorking() && !this._paused;
    }

    isPaused() {
        return this._paused;
    }

    get status() {
        return this._loader.status;
    }

    get extraData() {
        return this._extraData;
    }

    set extraData(data) {
        this._extraData = data;
    }

    // 【暴露出去的事件】--开始

    // prototype: function onDataArrival(chunks: ArrayBuffer, byteStart: number): number
    get onDataArrival() {
        return this._onDataArrival;
    }

    set onDataArrival(callback) {
        this._onDataArrival = callback;
    }

    get onSeeked() {
        return this._onSeeked;
    }

    set onSeeked(callback) {
        this._onSeeked = callback;
    }

    // prototype: function onError(type: number, info: {code: number, msg: string}): void
    get onError() {
        return this._onError;
    }

    set onError(callback) {
        this._onError = callback;
    }

    get onComplete() {
        return this._onComplete;
    }

    set onComplete(callback) {
        this._onComplete = callback;
    }

    get onRedirect() {
        return this._onRedirect;
    }

    set onRedirect(callback) {
        this._onRedirect = callback;
    }

    get onRecoveredEarlyEof() {
        return this._onRecoveredEarlyEof;
    }

    set onRecoveredEarlyEof(callback) {
        this._onRecoveredEarlyEof = callback;
    }

    // 【暴露出去的事件】--结束


    get currentURL() {
        return this._dataSource.url;
    }

    get hasRedirect() {
        return (this._redirectedURL != null || this._dataSource.redirectedURL != undefined);
    }

    get currentRedirectedURL() {
        return this._redirectedURL || this._dataSource.redirectedURL;
    }

    // in KB/s
    get currentSpeed() {
        // 如果是range方式，则从loader中获取，否则从_speedSampler中获取
        if (this._loaderClass === RangeLoader) {
            // SpeedSampler is inaccuracy if loader is RangeLoader
            return this._loader.currentSpeed;
        }
        return this._speedSampler.lastSecondKBps;
    }

    get loaderType() {
        return this._loader.type;
    }

    _selectSeekHandler() {
        let config = this._config;

        if (config.seekType === 'range') {
            this._seekHandler = new RangeSeekHandler(this._config.rangeLoadZeroStart);
        } else if (config.seekType === 'param') {
            let paramStart = config.seekParamStart || 'bstart';
            let paramEnd = config.seekParamEnd || 'bend';

            this._seekHandler = new ParamSeekHandler(paramStart, paramEnd);
        } else if (config.seekType === 'custom') {
            if (typeof config.customSeekHandler !== 'function') {
                throw new InvalidArgumentException('Custom seekType specified in config but invalid customSeekHandler!');
            }
            this._seekHandler = new config.customSeekHandler();
        } else {
            throw new InvalidArgumentException(`Invalid seekType in config: ${config.seekType}`);
        }
    }

    _selectLoader() {
        if (this._config.customLoader != null) {
            // 自定义方式，便于扩展
            this._loaderClass = this._config.customLoader;
        } else if (this._isWebSocketURL) {
            //判断url是不是ws协议， websocket方式
            this._loaderClass = WebSocketLoader;
        } else if (FetchStreamLoader.isSupported()) {
            // 常用的http方式加载
            this._loaderClass = FetchStreamLoader;
        } else if (MozChunkedLoader.isSupported()) {
            this._loaderClass = MozChunkedLoader;
        } else if (RangeLoader.isSupported()) {
            this._loaderClass = RangeLoader;
        } else {
            throw new RuntimeException('Your browser doesn\'t support xhr with arraybuffer responseType!');
        }
    }

    _createLoader() {
        this._loader = new this._loaderClass(this._seekHandler, this._config);
        if (this._loader.needStashBuffer === false) {
            this._enableStash = false;
        }
        // 知道总长度，点播模式下有值，直播模式下没有
        this._loader.onContentLengthKnown = this._onContentLengthKnown.bind(this);
        // 下载地址变了
        this._loader.onURLRedirect = this._onURLRedirect.bind(this);
        // 收到数据
        this._loader.onDataArrival = this._onLoaderChunkArrival.bind(this);
        // 下载完成
        this._loader.onComplete = this._onLoaderComplete.bind(this);
        // 下载出问题
        this._loader.onError = this._onLoaderError.bind(this);
    }

    open(optionalFrom) {
        // 从什么位置开始下载，-1说明一直下载
        this._currentRange = {from: 0, to: -1};
        if (optionalFrom) {
            this._currentRange.from = optionalFrom;
        }

        this._speedSampler.reset();
        if (!optionalFrom) {
            this._fullRequestFlag = true;
        }

        this._loader.open(this._dataSource, Object.assign({}, this._currentRange));
    }

    abort() {
        this._loader.abort();

        if (this._paused) {
            this._paused = false;
            this._resumeFrom = 0;
        }
    }

    pause() {
        if (this.isWorking()) {
            this._loader.abort();

            if (this._stashUsed !== 0) {
                this._resumeFrom = this._stashByteStart;
                this._currentRange.to = this._stashByteStart - 1;
            } else {
                this._resumeFrom = this._currentRange.to + 1;
            }
            this._stashUsed = 0;
            this._stashByteStart = 0;
            this._paused = true;
        }
    }

    resume() {
        if (this._paused) {
            this._paused = false;
            let bytes = this._resumeFrom;
            this._resumeFrom = 0;
            this._internalSeek(bytes, true);
        }
    }

    seek(bytes) {
        console.log('tdwu: seek to ' + bytes);
        this._paused = false;
        this._stashUsed = 0;
        this._stashByteStart = 0;
        this._internalSeek(bytes, true);
    }

    /**
     * When seeking request is from media seeking, unconsumed stash data should be dropped
     * However, stash data shouldn't be dropped if seeking requested from http reconnection
     *
     * @dropUnconsumed: Ignore and discard all unconsumed data in stash buffer
     */
    _internalSeek(bytes, dropUnconsumed) {
        if (this._loader.isWorking()) {
            this._loader.abort();
        }

        // dispatch & flush stash buffer before seek
        this._flushStashBuffer(dropUnconsumed);

        this._loader.destroy();
        this._loader = null;

        let requestRange = {from: bytes, to: -1};
        this._currentRange = {from: requestRange.from, to: -1};

        this._speedSampler.reset();
        this._stashSize = this._stashInitialSize;
        this._createLoader();
        this._loader.open(this._dataSource, requestRange);

        if (this._onSeeked) {
            this._onSeeked();
        }
    }

    updateUrl(url) {
        if (!url || typeof url !== 'string' || url.length === 0) {
            throw new InvalidArgumentException('Url must be a non-empty string!');
        }

        this._dataSource.url = url;

        // TODO: replace with new url
    }

    // 扩容buffer，缓冲区不够用时
    _expandBuffer(expectedBytes) {
        let bufferNewSize = this._stashSize;//存储的大小
        while (bufferNewSize + 1024 * 1024 * 1 < expectedBytes) {
            bufferNewSize *= 2;
        }

        bufferNewSize += 1024 * 1024 * 1;  // bufferSize = stashSize + 1MB
        if (bufferNewSize === this._bufferSize) {//buffer大小
            return;
        }

        let newBuffer = new ArrayBuffer(bufferNewSize);

        if (this._stashUsed > 0) {  // copy existing data into new buffer
            let stashOldArray = new Uint8Array(this._stashBuffer, 0, this._stashUsed);
            let stashNewArray = new Uint8Array(newBuffer, 0, bufferNewSize);
            stashNewArray.set(stashOldArray, 0);
        }

        this._stashBuffer = newBuffer;
        this._bufferSize = bufferNewSize;
    }

    _normalizeSpeed(input) {
        let list = this._speedNormalizeList;
        let last = list.length - 1;
        let mid = 0;
        let lbound = 0;
        let ubound = last;

        // 最低的速率值
        if (input < list[0]) {
            return list[0];
        }

        // binary search
        while (lbound <= ubound) {
            // 2分法查找
            mid = lbound + Math.floor((ubound - lbound) / 2);
            if (mid === last || (input >= list[mid] && input < list[mid + 1])) {
                return list[mid];
            } else if (list[mid] < input) {
                lbound = mid + 1;
            } else {
                ubound = mid - 1;
            }
        }
    }

    _adjustStashSize(normalized) {
        let stashSizeKB = 0;

        if (this._config.isLive) {
            // live stream: always use single normalized speed for size of stashSizeKB
            stashSizeKB = normalized;
        } else {
            if (normalized < 512) {
                stashSizeKB = normalized;
            } else if (normalized >= 512 && normalized <= 1024) {
                stashSizeKB = Math.floor(normalized * 1.5);
            } else {
                stashSizeKB = normalized * 2;
            }
        }

        if (stashSizeKB > 8192) {
            stashSizeKB = 8192;
        }

        let bufferSize = stashSizeKB * 1024 + 1024 * 1024 * 1;  // stashSize + 1MB
        if (this._bufferSize < bufferSize) {
            // 如果小了，先扩容
            this._expandBuffer(bufferSize);
        }
        this._stashSize = stashSizeKB * 1024;
    }

    _dispatchChunks(chunks, byteStart) {
        this._currentRange.to = byteStart + chunks.byteLength - 1;
        return this._onDataArrival(chunks, byteStart);
    }

    _onURLRedirect(redirectedURL) {
        this._redirectedURL = redirectedURL;
        if (this._onRedirect) {
            this._onRedirect(redirectedURL);
        }
    }

    _onContentLengthKnown(contentLength) {
        if (contentLength && this._fullRequestFlag) {
            this._totalLength = contentLength;
            this._fullRequestFlag = false;
        }
    }

    //byteStart 为chunk在整个流的开始index
    _onLoaderChunkArrival(chunk, byteStart, receivedLength) {
        this.lastByteStart = byteStart;// 记录上一次位置，onComplete是判断使用
        if (!this._onDataArrival) {
            throw new IllegalStateException('IOController: No existing consumer (onDataArrival) callback!');
        }
        if (this._paused) {
            return;
        }
        if (this._isEarlyEofReconnecting) {
            // Auto-reconnect for EarlyEof succeed, notify to upper-layer by callback
            this._isEarlyEofReconnecting = false;
            if (this._onRecoveredEarlyEof) {
                this._onRecoveredEarlyEof();
            }
        }

        // 累加收到的数量
        this._speedSampler.addBytes(chunk.byteLength);

        // 计算出下载的速度
        // adjust stash buffer size according to network speed dynamically
        let KBps = this._speedSampler.lastSecondKBps;
        if (KBps !== 0) {
            // 根据速率查找属于的参照标准速率
            let normalized = this._normalizeSpeed(KBps);
            if (this._speedNormalized !== normalized) {
                this._speedNormalized = normalized;
                // 如果所属的速率标准变了，重新分配暂存区大小。
                this._adjustStashSize(normalized);
            }
        }

        if (!this._enableStash) {  // disable stash
            // 【1】暂存区不可用的情况
            if (this._stashUsed === 0) {
                //【1.1】 暂存区没数据，直接转发数据
                // dispatch chunk directly to consumer;
                // check ret value (consumed bytes) and stash unconsumed to stashBuffer
                let consumed = this._dispatchChunks(chunk, byteStart);
                //【1.1.1】数据没消耗/使用完，加入“暂存区”
                if (consumed < chunk.byteLength) {  // unconsumed data remain.
                    // 保留（remain）没使用完的数据
                    let remain = chunk.byteLength - consumed;
                    if (remain > this._bufferSize) {
                        // 装不下，分配空间
                        this._expandBuffer(remain);
                    }
                    // 加入暂存区，但不切换模式，stash只是用来存放使用不完的数据
                    let stashArray = new Uint8Array(this._stashBuffer, 0, this._bufferSize);
                    // 从consumed开始开存放
                    stashArray.set(new Uint8Array(chunk, consumed), 0);
                    this._stashUsed += remain;// 有效数据
                    this._stashByteStart = byteStart + consumed;// 计算后，供下次_dispatchChunks传入。
                }
            } else {
                // 【1.2】暂存区由数据，先合并再转发
                // else: Merge chunk into stashBuffer, and dispatch stashBuffer to consumer.
                if (this._stashUsed + chunk.byteLength > this._bufferSize) {
                    this._expandBuffer(this._stashUsed + chunk.byteLength);
                }
                let stashArray = new Uint8Array(this._stashBuffer, 0, this._bufferSize);
                stashArray.set(new Uint8Array(chunk), this._stashUsed);
                this._stashUsed += chunk.byteLength;
                let consumed = this._dispatchChunks(this._stashBuffer.slice(0, this._stashUsed), this._stashByteStart);
                //【1.2.1】数据没消耗/使用完，加入“暂存区”
                if (consumed < this._stashUsed && consumed > 0) {  // unconsumed data remain
                    let remainArray = new Uint8Array(this._stashBuffer, consumed);
                    stashArray.set(remainArray, 0);
                }
                this._stashUsed -= consumed;
                this._stashByteStart += consumed;
            }
        } else {  // enable stash
            // 【2】 暂存区可用的情况
            if (this._stashUsed === 0 && this._stashByteStart === 0) {  // seeked? or init chunk?
                // This is the first chunk after seek action
                this._stashByteStart = byteStart;
            }

            if (this._stashUsed + chunk.byteLength <= this._stashSize) {
                //【2.1】缓冲区没满（溢出）。直接加入缓冲区
                // just stash
                let stashArray = new Uint8Array(this._stashBuffer, 0, this._stashSize);
                stashArray.set(new Uint8Array(chunk), this._stashUsed);
                this._stashUsed += chunk.byteLength;
            } else {  // stashUsed + chunkSize > stashSize, size limit exceeded
                //【2.2】缓冲区满了，开始转发数据
                let stashArray = new Uint8Array(this._stashBuffer, 0, this._bufferSize);
                if (this._stashUsed > 0) {  // There're stash datas in buffer
                    // dispatch the whole stashBuffer, and stash remain data
                    // then append chunk to stashBuffer (stash)
                    let buffer = this._stashBuffer.slice(0, this._stashUsed);
                    let consumed = this._dispatchChunks(buffer, this._stashByteStart);
                    if (consumed < buffer.byteLength) {
                        if (consumed > 0) {
                            let remainArray = new Uint8Array(buffer, consumed);
                            stashArray.set(remainArray, 0);
                            this._stashUsed = remainArray.byteLength;
                            this._stashByteStart += consumed;
                        }
                    } else {
                        this._stashUsed = 0;
                        this._stashByteStart += consumed;
                    }
                    if (this._stashUsed + chunk.byteLength > this._bufferSize) {
                        this._expandBuffer(this._stashUsed + chunk.byteLength);
                        stashArray = new Uint8Array(this._stashBuffer, 0, this._bufferSize);
                    }
                    stashArray.set(new Uint8Array(chunk), this._stashUsed);
                    this._stashUsed += chunk.byteLength;
                } else {  // stash buffer empty, but chunkSize > stashSize (oh, holy shit)
                    // dispatch chunk directly and stash remain data
                    let consumed = this._dispatchChunks(chunk, byteStart);
                    if (consumed < chunk.byteLength) {
                        let remain = chunk.byteLength - consumed;
                        if (remain > this._bufferSize) {
                            this._expandBuffer(remain);
                            stashArray = new Uint8Array(this._stashBuffer, 0, this._bufferSize);
                        }
                        stashArray.set(new Uint8Array(chunk, consumed), 0);
                        this._stashUsed += remain;
                        this._stashByteStart = byteStart + consumed;
                    }
                }
            }
        }
    }

    _flushStashBuffer(dropUnconsumed) {
        // 处理剩余的暂存区数据
        // 先转发一次，如果还有剩余的，再根据dropUnconsumed决定是否丢掉
        if (this._stashUsed > 0) {
            let buffer = this._stashBuffer.slice(0, this._stashUsed);
            // 先转发出去
            let consumed = this._dispatchChunks(buffer, this._stashByteStart);
            let remain = buffer.byteLength - consumed;

            if (consumed < buffer.byteLength) {
                if (dropUnconsumed) {
                    // 1 如果还有数据，就丢弃掉
                    Log.w(this.TAG, `${remain} bytes unconsumed data remain when flush buffer, dropped`);
                } else {
                    if (consumed > 0) {
                        //2 继续留到
                        let stashArray = new Uint8Array(this._stashBuffer, 0, this._bufferSize);
                        let remainArray = new Uint8Array(buffer, consumed);
                        stashArray.set(remainArray, 0);
                        this._stashUsed = remainArray.byteLength;
                        this._stashByteStart += consumed;
                    }
                    return 0;
                }
            }
            this._stashUsed = 0;
            this._stashByteStart = 0;
            return remain;
        }
        return 0;
    }

    _onLoaderComplete(from, to) {
        // Force-flush stash buffer, and drop unconsumed data

        this._flushStashBuffer(true);

        if (this.lastByteStart >= 0) {
            if (this._onComplete) {
                this._onComplete(this._extraData);
            }
        } else {
            if (this._onError) {
                this._onError(LoaderErrors.CONNECTING_TIMEOUT, {
                    code: 500,
                    msg: '无信号'
                });
            }
        }
    }

    _onLoaderError(type, data) {
        Log.e(this.TAG, `Loader error, code = ${data.code}, msg = ${data.msg}`);

        this._flushStashBuffer(false);

        if (this._isEarlyEofReconnecting) {
            // Auto-reconnect for EarlyEof failed, throw UnrecoverableEarlyEof error to upper-layer
            this._isEarlyEofReconnecting = false;
            type = LoaderErrors.UNRECOVERABLE_EARLY_EOF;
        }

        switch (type) {
            case LoaderErrors.EARLY_EOF: {
                if (!this._config.isLive) {
                    // Do internal http reconnect if not live stream
                    if (this._totalLength) {
                        let nextFrom = this._currentRange.to + 1;
                        if (nextFrom < this._totalLength) {
                            Log.w(this.TAG, 'Connection lost, trying reconnect...');
                            this._isEarlyEofReconnecting = true;
                            this._internalSeek(nextFrom, false);
                        }
                        return;
                    }
                    // else: We don't know totalLength, throw UnrecoverableEarlyEof
                }
                // live stream: throw UnrecoverableEarlyEof error to upper-layer
                type = LoaderErrors.UNRECOVERABLE_EARLY_EOF;
                break;
            }
            case LoaderErrors.UNRECOVERABLE_EARLY_EOF:
            case LoaderErrors.CONNECTING_TIMEOUT:
            case LoaderErrors.HTTP_STATUS_CODE_INVALID:
            case LoaderErrors.EXCEPTION:
                break;
        }

        if (this._onError) {
            this._onError(type, data);
        } else {
            throw new RuntimeException('IOException: ' + data.msg);
        }
    }

}

export default IOController;