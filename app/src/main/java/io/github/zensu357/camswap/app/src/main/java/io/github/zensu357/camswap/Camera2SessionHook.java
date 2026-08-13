package io.github.zensu357.camswap;

import android.graphics.SurfaceTexture;
import android.graphics.ImageFormat;
import android.hardware.camera2.CameraCaptureSession;
import android.hardware.camera2.CameraDevice;
import android.hardware.camera2.CaptureRequest;
import android.hardware.camera2.params.InputConfiguration;
import android.hardware.camera2.params.OutputConfiguration;
import android.hardware.camera2.params.SessionConfiguration;
import android.os.Build;
import android.os.Handler;
import android.os.HandlerThread;
import android.view.Surface;

import java.util.ArrayList;
import java.io.File;
import java.util.LinkedHashSet;
import java.util.Arrays;
import java.util.List;
import java.util.Locale;

import java.util.Collections;
import java.util.concurrent.ConcurrentHashMap;
import java.util.Set;
import java.util.Map;
import android.media.ImageWriter;
import android.media.Image;
import android.media.ImageReader;
import android.media.ImageReader.OnImageAvailableListener;
import android.media.MediaMetadataRetriever;
import android.os.SystemClock;
import android.graphics.Bitmap;
import android.graphics.Rect;
import java.io.ByteArrayOutputStream;
import java.lang.reflect.Method;
import java.nio.ByteBuffer;

import io.github.zensu357.camswap.utils.LogUtil;
import io.github.zensu357.camswap.utils.VideoManager;

import io.github.zensu357.camswap.api101.Api101Runtime;

/**
 * Handles Camera2 session interception: replaces real camera surfaces with
 * a virtual surface, then starts video playback via {@link MediaPlayerManager}.
 */
public final class Camera2SessionHook {
    private static final int WHATSAPP_YUV_BRIDGE_MAX_IMAGES = 8;

    /**
     * YUV å¸§ç¼“å­˜åˆ·æ–°é—´éš”ï¼ˆæ¯«ç§’ï¼‰ã€‚
     * GL æ¸²æŸ“å™¨å¯ç”¨æ—¶ä½¿ç”¨è¾ƒçŸ­é—´éš”ä»¥ä¿æŒç”»é¢æµç•…ï¼›
     * å›žé€€åˆ° MediaMetadataRetriever æ—¶è‡ªåŠ¨ä½¿ç”¨è¾ƒé•¿é—´éš”ï¼Œé¿å…é˜»å¡žæ³µçº¿ç¨‹ã€‚
     */
    private static final long YUV_CACHE_REFRESH_GL_MS = 66L;
    private static final long YUV_CACHE_REFRESH_FALLBACK_MS = 200L;

    private final MediaPlayerManager playerManager;
    private volatile String currentPackageName;
    private volatile String currentActivityClassName;

    // Camera2 surfaces
    Surface previewSurface;
    Surface previewSurface1;
    Surface readerSurface;
    Surface readerSurface1;

    // Tracker for Photo Fake
    public final Set<Surface> trackedReaderSurfaces = Collections
            .newSetFromMap(new ConcurrentHashMap<Surface, Boolean>());
    public final Map<Surface, ImageWriter> imageWriterMap = new ConcurrentHashMap<>();
    public final Map<Surface, Integer> surfaceFormatMap = new ConcurrentHashMap<>();
    public final Map<Surface, int[]> surfaceSizeMap = new ConcurrentHashMap<>();
    private final Map<Surface, CachedYuvFrame> cachedYuvFrameMap = new ConcurrentHashMap<>();
    private final Map<Surface, FakeYuvBridge> fakeYuvBridgeMap = new ConcurrentHashMap<>();
    private final Set<Surface> internalFakeYuvReaderSurfaces = Collections
            .newSetFromMap(new ConcurrentHashMap<Surface, Boolean>());
    public final Set<Surface> pendingJpegSurfaces = Collections
            .newSetFromMap(new ConcurrentHashMap<Surface, Boolean>());
    private final Set<String> hookedStateCallbackClasses = Collections
            .newSetFromMap(new ConcurrentHashMap<String, Boolean>());
    private final Set<String> hookedDeviceClasses = Collections
            .newSetFromMap(new ConcurrentHashMap<String, Boolean>());
    private final Set<String> hookedSessionCallbackClasses = Collections
            .newSetFromMap(new ConcurrentHashMap<String, Boolean>());
    private volatile long lastWhatsAppYuvSuccessLogMs = 0L;
    private volatile long lastWhatsAppYuvPlaceholderLogMs = 0L;
    private volatile long lastNoGlRendererLogMs = 0L;
    private volatile long lastGlBlackFallbackLogMs = 0L;
    private volatile long lastGlNullFallbackLogMs = 0L;
    private volatile long lastYuvKeepLogMs = 0L;
    /** ä¸Šä¸€æ¬¡ YUV å¸§æ˜¯å¦é€šè¿‡å›žé€€è·¯å¾„ï¼ˆè§†é¢‘æ–‡ä»¶æˆªå¸§ï¼‰ç”Ÿæˆ */
    private volatile boolean lastYuvFrameWasFallback = true;
    /** YUV å¸§çŽ‡ç»Ÿè®¡ */
    private volatile int yuvFrameCount = 0;
    private volatile long yuvFpsWindowStartMs = 0L;
    private final Map<ImageReader, YuvCallbackPump> whatsappYuvPumpMap = new ConcurrentHashMap<>();
    private HandlerThread whatsappYuvPumpThread;
    private Handler whatsappYuvPumpHandler;

    // Photo Fake: ç­‰å¾… build() æ—¶è§¦å‘
    public volatile Surface pendingPhotoSurface;
    private volatile boolean bypassCurrentSession = false;
    /** æ ‡è®°æ­£åœ¨é‡Šæ”¾èµ„æºï¼Œé˜²æ­¢é‡Šæ”¾æœŸé—´ç«žæ€åˆ›å»ºæ–°æ¡¥æŽ¥ */
    private volatile boolean isReleasing = false;

    // Deferred playback: set when build() fires before addTarget()
    volatile boolean pendingPlayback = false;
    private volatile boolean yuvBridgeSessionReady = false;

    // Surface-change tracking: skip redundant initCamera2Players when surfaces unchanged
    private Surface lastInitReader, lastInitReader1, lastInitPreview, lastInitPreview1;

    // Virtual surface for session hijacking
    private Surface virtualSurface;
    private SurfaceTexture virtualTexture;
    private HandlerThread virtualSurfaceDrainThread;
    private Handler virtualSurfaceDrainHandler;
    private boolean needRecreate;
    private final ThreadLocal<Integer> fakeYuvAcquireDepth = new ThreadLocal<Integer>() {
        @Override
        protected Integer initialValue() {
            return 0;
        }
    };
    private final ThreadLocal<Integer> internalBridgeCreationDepth = new ThreadLocal<Integer>() {
        @Override
        protected Integer initialValue() {
            return 0;
        }
    };

    /** Public accessor for Camera2Handler to check/redirect surfaces. */
    public Surface getVirtualSurface() {
        return virtualSurface;
    }

    /** Mark virtual surface for recreation on next session creation. */
    public void invalidateVirtualSurface() {
        needRecreate = true;
    }

    /**
     * Ensure the virtual surface exists. Called lazily from addTarget/session hooks
     * in case onOpened hook didn't fire (ART optimization on obfuscated classes).
     */
    public Surface ensureVirtualSurface() {
        if (virtualSurface == null || !virtualSurface.isValid()) {
            needRecreate = true;
            createVirtualSurface();
            LogUtil.log("ã€CSã€‘å»¶è¿Ÿåˆ›å»ºè™šæ‹Ÿ Surfaceï¼ˆonOpened æœªè§¦å‘å›žé€€ï¼‰");
        }
        return virtualSurface;
    }

    // Session config
    CaptureRequest.Builder captureBuilder;
    SessionConfiguration fakeSessionConfig;
    SessionConfiguration realSessionConfig;
    OutputConfiguration outputConfig;
    boolean isFirstHookBuild = true;

    public Camera2SessionHook(MediaPlayerManager playerManager) {
        this.playerManager = playerManager;
    }

    public void setCurrentPackageName(String packageName) {
        currentPackageName = packageName;
        playerManager.setPackageName(packageName);
    }

    public void setCurrentActivityClassName(String activityClassName) {
        currentActivityClassName = activityClassName;
    }

    private boolean isWhatsAppPackage(String packageName) {
        return packageName != null && packageName.toLowerCase(Locale.ROOT).contains("whatsapp");
    }

    private boolean isLinePackage(String packageName) {
        if (packageName == null || packageName.isEmpty()) {
            return false;
        }
        String normalized = packageName.toLowerCase(Locale.ROOT);
        return normalized.equals("jp.naver.line.android")
                || normalized.startsWith("jp.naver.line.android:")
                || normalized.contains("line");
    }

    private boolean shouldUseFakeYuvBridgeForPackage(String packageName) {
        return isWhatsAppPackage(packageName) || isLinePackage(packageName);
    }

    private boolean isVoipActivity() {
        return currentActivityClassName != null
                && currentActivityClassName.contains("VoIPServiceActivity");
    }

    private boolean shouldUseYuvPumpForSurface(Surface surface) {
        if (surface == null || !isYuvReaderSurface(surface) || isVoipActivity()) {
            return false;
        }
        return isCurrentSessionYuvReaderSurface(surface);
    }

    private String getCurrentPackageName() {
        if (currentPackageName != null && !currentPackageName.isEmpty()) {
            return currentPackageName;
        }
        return HookMain.toast_content != null ? HookMain.toast_content.getPackageName() : null;
    }

    public boolean isCurrentSessionBypassed() {
        return bypassCurrentSession;
    }

    private void setBypassCurrentSession(boolean bypass) {
        bypassCurrentSession = bypass;
    }

    /** Called by Camera2Handler when onOpened fires on the state callback class. */
    public void hookStateCallback(Class<?> hookedClass) {
        if (hookedClass == null) {
            return;
        }
        if (!hookedStateCallbackClasses.add(hookedClass.getName())) {
            return;
        }

        // onOpened
        try {
            Method m = resolveMethodOnClass(hookedClass, "onOpened", CameraDevice.class);
            Api101Runtime.requireModule().hook(m).intercept(chain -> {
                Object[] args = toArgs(chain.getArgs());
                try {
                    isReleasing = false;
                    needRecreate = true;
                    createVirtualSurface();
                    playerManager.releaseCamera2Resources();
                    releaseImageWriters(false);
                    previewSurface1 = null;
                    readerSurface1 = null;
                    readerSurface = null;
                    previewSurface = null;
                    pendingPlayback = false;
                    captureBuilder = null;
                    setBypassCurrentSession(false);
                    yuvBridgeSessionReady = false;
                    isFirstHookBuild = true;
                    lastInitReader = null;
                    lastInitReader1 = null;
                    lastInitPreview = null;
                    lastInitPreview1 = null;
                    LogUtil.log("ã€CSã€‘æ‰“å¼€ç›¸æœºC2");

                    File file = new File(VideoManager.getCurrentVideoPath());
                    // If video not found, provider may have started since init â€”
                    // retry once before giving up
                    if (!file.exists() && !VideoManager.isProviderAvailable()) {
                        VideoManager.checkProviderAvailability();
                        if (VideoManager.isProviderAvailable()) {
                            VideoManager.getConfig().forceReload();
                            VideoManager.updateVideoPath(false);
                            file = new File(VideoManager.getCurrentVideoPath());
                            LogUtil.log("ã€CSã€‘onOpened å»¶è¿ŸèŽ·å– Provider æˆåŠŸï¼Œè§†é¢‘è·¯å¾„: " + file.getAbsolutePath());
                        }
                    }
                    boolean showToast = !VideoManager.getConfig().getBoolean(ConfigManager.KEY_DISABLE_TOAST, false);
                    if (!file.exists()) {
                        if (HookMain.toast_content != null && showToast) {
                            try {
                                LogUtil.log("ã€CSã€‘ä¸å­˜åœ¨æ›¿æ¢è§†é¢‘: " + HookMain.toast_content.getPackageName()
                                        + " å½“å‰è·¯å¾„ï¼š" + VideoManager.video_path);
                            } catch (Exception ee) {
                                LogUtil.log("ã€CSã€‘[toast]" + ee);
                            }
                        }
                        return chain.proceed(args);
                    }

                    hookAllCreateSessionVariants(args[0].getClass());
                } catch (Throwable t) {
                    LogUtil.log("ã€CSã€‘onOpened before å¼‚å¸¸: " + t);
                }
                return chain.proceed(args);
            });
        } catch (Throwable t) {
            LogUtil.log("ã€CSã€‘Hook onOpened å¤±è´¥: " + t);
        }

        // onClosed
        try {
            Method m = resolveMethodOnClass(hookedClass, "onClosed", CameraDevice.class);
            Api101Runtime.requireModule().hook(m).intercept(chain -> {
                Object[] args = toArgs(chain.getArgs());
                try {
                    LogUtil.log("ã€CSã€‘ç›¸æœºå…³é—­ onClosedï¼Œé‡Šæ”¾æ’­æ”¾å™¨èµ„æº");
                    setBypassCurrentSession(false);
                    yuvBridgeSessionReady = false;
                    stopAllWhatsAppYuvPumps();
                    playerManager.releaseCamera2Resources();
                    releaseImageWriters();
                } catch (Throwable t) {
                    LogUtil.log("ã€CSã€‘onClosed before å¼‚å¸¸: " + t);
                }
                return chain.proceed(args);
            });
        } catch (Throwable t) {
            LogUtil.log("ã€CSã€‘Hook onClosed å¤±è´¥: " + t);
        }

        // onError
        try {
            Method m = resolveMethodOnClass(hookedClass, "onError", CameraDevice.class, int.class);
            Api101Runtime.requireModule().hook(m).intercept(chain -> {
                Object[] args = toArgs(chain.getArgs());
                try {
                    LogUtil.log("ã€CSã€‘ç›¸æœºé”™è¯¯onerrorï¼š" + (int) args[1]);
                } catch (Throwable t) {
                    LogUtil.log("ã€CSã€‘onError before å¼‚å¸¸: " + t);
                }
                return chain.proceed(args);
            });
        } catch (Throwable t) {
            LogUtil.log("ã€CSã€‘Hook onError å¤±è´¥: " + t);
        }

        // onDisconnected
        try {
            Method m = resolveMethodOnClass(hookedClass, "onDisconnected", CameraDevice.class);
            Api101Runtime.requireModule().hook(m).intercept(chain -> {
                Object[] args = toArgs(chain.getArgs());
                try {
                    LogUtil.log("ã€CSã€‘ç›¸æœºæ–­å¼€ onDisconnectedï¼Œé‡Šæ”¾æ’­æ”¾å™¨èµ„æº");
                    setBypassCurrentSession(false);
                    yuvBridgeSessionReady = false;
                    stopAllWhatsAppYuvPumps();
                    playerManager.releaseCamera2Resources();
                    releaseImageWriters();
                } catch (Throwable t) {
                    LogUtil.log("ã€CSã€‘onDisconnected before å¼‚å¸¸: " + t);
                }
                return chain.proceed(args);
            });
        } catch (Throwable t) {
            LogUtil.log("ã€CSã€‘Hook onDisconnected å¤±è´¥: " + t);
        }
    }

    /** Start video playback on all current surfaces. */
    public void startPlayback() {
        if (readerSurface == null && readerSurface1 == null
                && previewSurface == null && previewSurface1 == null) {
            LogUtil.log("ã€CSã€‘å»¶è¿Ÿæ’­æ”¾ï¼šæ‰€æœ‰ surface ä¸ºç©ºï¼Œç­‰å¾… addTarget");
            pendingPlayback = true;
            return;
        }
        // Skip redundant init when surfaces haven't changed since last call
        if (readerSurface == lastInitReader && readerSurface1 == lastInitReader1
                && previewSurface == lastInitPreview && previewSurface1 == lastInitPreview1) {
            LogUtil.log("ã€CSã€‘è·³è¿‡é‡å¤ startPlaybackï¼šsurface æœªå˜åŒ–");
            pendingPlayback = false;
            return;
        }
        lastInitReader = readerSurface;
        lastInitReader1 = readerSurface1;
        lastInitPreview = previewSurface;
        lastInitPreview1 = previewSurface1;
        pendingPlayback = false;
        playerManager.initCamera2Players(readerSurface, readerSurface1,
                previewSurface, previewSurface1);
        markYuvBridgeSessionReadyIfPossible();

        // WhatsApp è§†é¢‘é€šè¯ï¼šé¢„è§ˆæ¸²æŸ“å™¨æ—‹è½¬è®¾ä¸º 0Â°ï¼Œè®©æœ¬æœºè‡ªæ‹ç”»é¢æ–¹å‘æ­£ç¡®ã€‚
        // YUV æˆªå¸§æ—¶é€šè¿‡ captureFrameWithRotation å•ç‹¬åº”ç”¨ video_rotation_offsetï¼Œ
        // ç¡®ä¿å¯¹æ–¹çœ‹åˆ°æ­£ç¡®æ–¹å‘ã€‚
        if (isWhatsAppPackage(getCurrentPackageName()) && !whatsappYuvPumpMap.isEmpty()) {
            MediaPlayerManager pm = HookMain.playerManager;
            if (pm.c2_renderer != null) pm.c2_renderer.setRotation(0);
            if (pm.c2_renderer_1 != null) pm.c2_renderer_1.setRotation(0);
            LogUtil.log("ã€CSã€‘WhatsApp è§†é¢‘é€šè¯ï¼šé¢„è§ˆæ¸²æŸ“å™¨æ—‹è½¬å·²è®¾ä¸º 0Â°");
        }
    }

    public void registerImageReaderSurface(Surface surface, int format, int width, int height) {
        if (surface == null) {
            return;
        }
        trackedReaderSurfaces.add(surface);
        surfaceFormatMap.put(surface, format);
        surfaceSizeMap.put(surface, new int[] { width, height });
    }

    public boolean isTrackedReaderSurface(Surface surface) {
        return surface != null && trackedReaderSurfaces.contains(surface);
    }

    public boolean isJpegReaderSurface(Surface surface) {
        Integer format = surfaceFormatMap.get(surface);
        return format != null && format == ImageFormat.JPEG;
    }

    public boolean shouldKeepRealReaderSurface(Surface surface) {
        return isJpegReaderSurface(surface);
    }

    public boolean shouldKeepRealReaderSurfaceForPackage(Surface surface, String packageName) {
        if (!isTrackedReaderSurface(surface)) {
            return false;
        }
        return isJpegReaderSurface(surface);
    }

    public boolean shouldKeepRealReaderSurfaceForCurrentPackage(Surface surface) {
        return shouldKeepRealReaderSurfaceForPackage(surface, getCurrentPackageName());
    }

    private boolean shouldKeepYuvReaderSurfaceForPackage(Surface surface, String packageName) {
        // CameraX-style preview/analysis pipelines often consume YUV ImageReader frames
        // directly. Package allowlists proved too brittle for LINE's camera variants, so
        // keep all tracked YUV reader surfaces on the real session output and feed them via
        // the fake YUV bridge instead of redirecting them to the GL preview surface.
        return isYuvReaderSurface(surface)
                && !isInternalFakeYuvReaderSurface(surface);
    }

    private boolean isCurrentSessionYuvReaderSurface(Surface surface) {
        if (surface == null) {
            return false;
        }
        return surface.equals(readerSurface) || surface.equals(readerSurface1);
    }

    private boolean shouldDriveYuvBridgeNow() {
        return !isReleasing && yuvBridgeSessionReady;
    }

    public boolean shouldKeepYuvReaderSurfaceForCurrentPackage(Surface surface) {
        boolean keep = shouldKeepYuvReaderSurfaceForPackage(surface, getCurrentPackageName());
        if (surface != null && isYuvReaderSurface(surface)) {
            maybeLogYuvKeepDecision(surface, keep);
        }
        return keep;
    }

    private void maybeLogYuvKeepDecision(Surface surface, boolean keep) {
        long now = SystemClock.elapsedRealtime();
        if (now - lastYuvKeepLogMs < 1000L) {
            return;
        }
        lastYuvKeepLogMs = now;
        LogUtil.log("ã€CSã€‘YUV keep åˆ¤å®š: pkg=" + getCurrentPackageName()
                + " keep=" + keep + " surface=" + surface);
    }

    public boolean shouldSkipImageReaderTracking() {
        return internalBridgeCreationDepth.get() > 0;
    }

    public boolean shouldBypassYuvAcquireHook(Surface surface) {
        return fakeYuvAcquireDepth.get() > 0 || isInternalFakeYuvReaderSurface(surface);
    }

    public boolean isInternalFakeYuvReaderSurface(Surface surface) {
        return surface != null && internalFakeYuvReaderSurfaces.contains(surface);
    }

    private void enterInternalBridgeCreation() {
        internalBridgeCreationDepth.set(internalBridgeCreationDepth.get() + 1);
    }

    private void exitInternalBridgeCreation() {
        int depth = internalBridgeCreationDepth.get();
        if (depth <= 1) {
            internalBridgeCreationDepth.remove();
        } else {
            internalBridgeCreationDepth.set(depth - 1);
        }
    }

    private void enterFakeYuvAcquire() {
        fakeYuvAcquireDepth.set(fakeYuvAcquireDepth.get() + 1);
    }

    private void exitFakeYuvAcquire() {
        int depth = fakeYuvAcquireDepth.get();
        if (depth <= 1) {
            fakeYuvAcquireDepth.remove();
        } else {
            fakeYuvAcquireDepth.set(depth - 1);
        }
    }

    public boolean shouldUseReaderPlaybackSurfaceForPackage(String packageName) {
        return !shouldUseFakeYuvBridgeForPackage(packageName);
    }

    public boolean isYuvReaderSurface(Surface surface) {
        Integer format = surfaceFormatMap.get(surface);
        return format != null && format == ImageFormat.YUV_420_888;
    }

    private Surface getOutputSurface(Object output) {
        if (output instanceof Surface) {
            return (Surface) output;
        }
        if (output instanceof OutputConfiguration) {
            return ((OutputConfiguration) output).getSurface();
        }
        return null;
    }

    private boolean shouldBypassWhatsAppYuvSession(List<?> outputs, String packageName) {
        // ä¸å†éœ€è¦æ•´ä½“æ—è·¯ sessionï¼šYUV reader surface çŽ°åœ¨ç›´æŽ¥ä¿ç•™åœ¨ session è¾“å‡ºä¸­ï¼Œ
        // preview surface ä»ç„¶æ›¿æ¢ä¸ºè™šæ‹Ÿ surfaceã€‚è¿™æ · Camera HAL ä¼šä¸º YUV reader
        // äº§å‡ºæ­£ç¡®æ ¼å¼çš„å¸§ï¼ŒåŒæ—¶ preview ä»ç„¶æ˜¾ç¤ºæˆ‘ä»¬çš„æ›¿æ¢è§†é¢‘ã€‚
        return false;
    }

    private void enableSessionBypass(String reason) {
        if (!bypassCurrentSession) {
            LogUtil.log("ã€CSã€‘å¯ç”¨ YUV ä¼šè¯æ—è·¯: " + reason);
        }
        setBypassCurrentSession(true);
        pendingPlayback = false;
        previewSurface = null;
        previewSurface1 = null;
        readerSurface = null;
        readerSurface1 = null;
        playerManager.releaseCamera2Resources();
    }

    private void disableSessionBypass() {
        setBypassCurrentSession(false);
    }

    public void rememberPreviewSurface(Surface surface) {
        if (surface == null || isTrackedReaderSurface(surface)) {
            return;
        }
        if (previewSurface == null) {
            previewSurface = surface;
        } else if (!previewSurface.equals(surface) && previewSurface1 == null) {
            // For packages without fake YUV bridge support, only use one preview surface to avoid
            // rendering RGBA to untracked ImageReader surfaces (CameraX apps
            // like LINE may expose a second reader-backed target here).
            if (shouldUseFakeYuvBridgeForPackage(getCurrentPackageName())) {
                previewSurface1 = surface;
            } else {
                LogUtil.log("ã€CSã€‘è·³è¿‡ç¬¬äºŒä¸ª preview surface (æ—  YUV å…¼å®¹): " + surface);
            }
        }
        if (pendingPlayback) {
            LogUtil.log("ã€CSã€‘addTarget è§¦å‘å»¶è¿Ÿæ’­æ”¾ (preview)");
            startPlayback();
        }
    }

    public void rememberReaderPlaybackSurface(Surface surface) {
        if (!shouldUseReaderPlaybackSurfaceForPackage(getCurrentPackageName())) {
            return;
        }
        if (surface == null || shouldKeepRealReaderSurface(surface)) {
            return;
        }
        // Skip YUV ImageReader surfaces for packages without fake YUV bridge support:
        // GLVideoRenderer outputs RGBA which causes format mismatch crash
        // when CameraX acquires images from a YUV_420_888 ImageReader.
        if (isYuvReaderSurface(surface) && !shouldUseFakeYuvBridgeForPackage(getCurrentPackageName())) {
            LogUtil.log("ã€CSã€‘è·³è¿‡ YUV reader surface ä½œä¸ºæ’­æ”¾ç›®æ ‡ (æ—  YUV å…¼å®¹): " + surface);
            return;
        }
        if (readerSurface == null) {
            readerSurface = surface;
        } else if (!readerSurface.equals(surface) && readerSurface1 == null) {
            readerSurface1 = surface;
        }
        if (pendingPlayback) {
            LogUtil.log("ã€CSã€‘addTarget è§¦å‘å»¶è¿Ÿæ’­æ”¾ (reader)");
            startPlayback();
        }
    }

    public void onTargetRemoved(Surface surface) {
        if (surface == null) {
            return;
        }
        pendingJpegSurfaces.remove(surface);
        if (surface.equals(previewSurface)) {
            previewSurface = null;
        }
        if (surface.equals(previewSurface1)) {
            previewSurface1 = null;
        }
        if (surface.equals(readerSurface)) {
            readerSurface = null;
        }
        if (surface.equals(readerSurface1)) {
            readerSurface1 = null;
        }
    }

    public void markPendingJpegCapture(Surface surface) {
        if (shouldKeepRealReaderSurface(surface)) {
            pendingJpegSurfaces.add(surface);
            pendingPhotoSurface = surface;
        }
    }

    // =====================================================================
    // Virtual surface management
    // =====================================================================

    private Surface createVirtualSurface() {
        if (needRecreate) {
            if (virtualTexture != null) {
                virtualTexture.release();
                virtualTexture = null;
            }
            if (virtualSurface != null) {
                virtualSurface.release();
                virtualSurface = null;
            }
            // Ensure a drain thread exists to consume camera HAL frames,
            // preventing buffer queue stall and native crash.
            if (virtualSurfaceDrainThread == null) {
                virtualSurfaceDrainThread = new HandlerThread("CS-VirtualDrain");
                virtualSurfaceDrainThread.start();
                virtualSurfaceDrainHandler = new Handler(virtualSurfaceDrainThread.getLooper());
            }
            virtualTexture = new SurfaceTexture(15);
            virtualTexture.setDefaultBufferSize(1920, 1080);
            virtualTexture.setOnFrameAvailableListener(st -> {
                try {
                    st.updateTexImage();
                } catch (Exception ignored) {
                }
            }, virtualSurfaceDrainHandler);
            virtualSurface = new Surface(virtualTexture);
            needRecreate = false;
        } else {
            if (virtualSurface == null) {
                needRecreate = true;
                virtualSurface = createVirtualSurface();
            }
        }
        LogUtil.log("ã€CSã€‘ã€é‡å»ºè™šæ‹ŸSurfaceã€‘" + virtualSurface);
        return virtualSurface;
    }

    private Surface getSessionSurface(Surface surface) {
        if (shouldKeepRealReaderSurface(surface)) {
            return surface;
        }
        return createVirtualSurface();
    }

    private Surface getSessionSurface(Surface surface, String packageName) {
        if (shouldKeepRealReaderSurfaceForPackage(surface, packageName)) {
            return surface;
        }
        return createVirtualSurface();
    }

    private List<Surface> rewriteSessionSurfaces(List<?> outputs) {
        return rewriteSessionSurfaces(outputs, getCurrentPackageName());
    }

    private List<Surface> rewriteSessionSurfaces(List<?> outputs, String packageName) {
        LinkedHashSet<Surface> rewritten = new LinkedHashSet<>();
        if (outputs != null) {
            for (Object output : outputs) {
                if (output instanceof Surface) {
                    Surface surface = (Surface) output;
                    if (shouldKeepYuvReaderSurfaceForPackage(surface, packageName)) {
                        rewritten.add(surface);
                        LogUtil.log("ã€CSã€‘Session ä¿ç•™ YUV reader surface: " + surface);
                    } else {
                        rewritten.add(getSessionSurface(surface, packageName));
                    }
                }
            }
        }
        if (rewritten.isEmpty()) {
            rewritten.add(createVirtualSurface());
        }
        return new ArrayList<>(rewritten);
    }

    private OutputConfiguration createOutputConfiguration(OutputConfiguration original, Surface surface) {
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.N) {
            try {
                return new OutputConfiguration(original.getSurfaceGroupId(), surface);
            } catch (Throwable ignored) {
            }
        }
        return new OutputConfiguration(surface);
    }

    private List<OutputConfiguration> rewriteOutputConfigurations(List<?> outputs) {
        return rewriteOutputConfigurations(outputs, getCurrentPackageName());
    }

    private List<OutputConfiguration> rewriteOutputConfigurations(List<?> outputs, String packageName) {
        List<OutputConfiguration> rewritten = new ArrayList<>();
        boolean hasVirtualOutput = false;
        if (outputs != null) {
            for (Object output : outputs) {
                if (!(output instanceof OutputConfiguration)) {
                    continue;
                }
                OutputConfiguration config = (OutputConfiguration) output;
                Surface originalSurface = config.getSurface();
                if (shouldKeepRealReaderSurfaceForPackage(originalSurface, packageName)
                        || shouldKeepYuvReaderSurfaceForPackage(originalSurface, packageName)) {
                    rewritten.add(createOutputConfiguration(config, originalSurface));
                    if (shouldKeepYuvReaderSurfaceForPackage(originalSurface, packageName)) {
                        LogUtil.log("ã€CSã€‘OutputConfig ä¿ç•™ YUV reader surface: " + originalSurface);
                    }
                } else if (!hasVirtualOutput) {
                    rewritten.add(createOutputConfiguration(config, createVirtualSurface()));
                    hasVirtualOutput = true;
                }
            }
        }
        if (rewritten.isEmpty()) {
            rewritten.add(new OutputConfiguration(createVirtualSurface()));
        }
        return rewritten;
    }

    private SessionConfiguration rewriteSessionConfiguration(SessionConfiguration sessionConfiguration) {
        String packageName = getCurrentPackageName();
        List<OutputConfiguration> outputs = rewriteOutputConfigurations(sessionConfiguration.getOutputConfigurations(),
                packageName);
        SessionConfiguration rewritten = new SessionConfiguration(
                sessionConfiguration.getSessionType(),
                outputs,
                sessionConfiguration.getExecutor(),
                sessionConfiguration.getStateCallback());
        try {
            InputConfiguration inputConfiguration = sessionConfiguration.getInputConfiguration();
            if (inputConfiguration != null) {
                rewritten.setInputConfiguration(inputConfiguration);
            }
        } catch (Throwable ignored) {
        }
        try {
            CaptureRequest sessionParameters = sessionConfiguration.getSessionParameters();
            if (sessionParameters != null) {
                rewritten.setSessionParameters(sessionParameters);
            }
        } catch (Throwable ignored) {
        }
        return rewritten;
    }

    // =====================================================================
    // Hook all createCaptureSession variants
    // =====================================================================

    void hookAllCreateSessionVariants(Class<?> deviceClass) {
        if (deviceClass == null) {
            return;
        }
        if (!hookedDeviceClasses.add(deviceClass.getName())) {
            return;
        }

        // 1. createCaptureSession(List, StateCallback, Handler)
        try {
            Method m = resolveMethodOnClass(deviceClass, "createCaptureSession",
                    List.class, CameraCaptureSession.StateCallback.class, Handler.class);
            Api101Runtime.requireModule().hook(m).intercept(chain -> {
                Object[] args = toArgs(chain.getArgs());
                try {
                    if (args[0] != null) {
                        if (HookGuards.shouldBypass(getCurrentPackageName(), HookGuards.getCurrentVideoFile())) {
                            yuvBridgeSessionReady = false;
                            return chain.proceed(args);
                        }
                        if (shouldBypassWhatsAppYuvSession((List<?>) args[0], getCurrentPackageName())) {
                            enableSessionBypass("createCaptureSession(List)");
                        } else {
                            disableSessionBypass();
                        }
                        LogUtil.log("ã€CSã€‘createCaptureSessionåˆ›å»ºæ•èŽ·ï¼ŒåŽŸå§‹:" + args[0] + "è™šæ‹Ÿï¼š" + virtualSurface);
                        if (!isCurrentSessionBypassed()) {
                            args[0] = rewriteSessionSurfaces((List<?>) args[0]);
                        }
                        if (args[1] != null)
                            hookSessionCallback((CameraCaptureSession.StateCallback) args[1]);
                    }
                } catch (Throwable t) {
                    LogUtil.log("ã€CSã€‘createCaptureSession(List) before å¼‚å¸¸: " + t);
                }
                return chain.proceed(args);
            });
        } catch (Throwable t) {
            LogUtil.log("ã€CSã€‘Hook createCaptureSession(List) å¤±è´¥: " + t);
        }

        // 2. createCaptureSessionByOutputConfigurations (API 24+)
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.N) {
            try {
                Method m = resolveMethodOnClass(deviceClass,
                        "createCaptureSessionByOutputConfigurations",
                        List.class, CameraCaptureSession.StateCallback.class, Handler.class);
                Api101Runtime.requireModule().hook(m).intercept(chain -> {
                    Object[] args = toArgs(chain.getArgs());
                    try {
                        if (args[0] != null) {
                            if (HookGuards.shouldBypass(getCurrentPackageName(), HookGuards.getCurrentVideoFile())) {
                                yuvBridgeSessionReady = false;
                                return chain.proceed(args);
                            }
                            if (shouldBypassWhatsAppYuvSession((List<?>) args[0], getCurrentPackageName())) {
                                enableSessionBypass("createCaptureSessionByOutputConfigurations");
                            } else {
                                disableSessionBypass();
                            }
                            if (!isCurrentSessionBypassed()) {
                                args[0] = rewriteOutputConfigurations((List<?>) args[0]);
                            }
                            LogUtil.log("ã€CSã€‘æ‰§è¡Œäº†createCaptureSessionByOutputConfigurations");
                            if (args[1] != null)
                                hookSessionCallback((CameraCaptureSession.StateCallback) args[1]);
                        }
                    } catch (Throwable t) {
                        LogUtil.log("ã€CSã€‘createCaptureSessionByOutputConfigurations before å¼‚å¸¸: " + t);
                    }
                    return chain.proceed(args);
                });
            } catch (Throwable t) {
                LogUtil.log("ã€CSã€‘Hook createCaptureSessionByOutputConfigurations å¤±è´¥: " + t);
            }
        }

        // 3. createConstrainedHighSpeedCaptureSession
        try {
            Method m = resolveMethodOnClass(deviceClass, "createConstrainedHighSpeedCaptureSession",
                    List.class, CameraCaptureSession.StateCallback.class, Handler.class);
            Api101Runtime.requireModule().hook(m).intercept(chain -> {
                Object[] args = toArgs(chain.getArgs());
                try {
                    if (args[0] != null) {
                        if (HookGuards.shouldBypass(getCurrentPackageName(), HookGuards.getCurrentVideoFile())) {
                            yuvBridgeSessionReady = false;
                            return chain.proceed(args);
                        }
                        if (shouldBypassWhatsAppYuvSession((List<?>) args[0], getCurrentPackageName())) {
                            enableSessionBypass("createConstrainedHighSpeedCaptureSession");
                        } else {
                            disableSessionBypass();
                        }
                        if (!isCurrentSessionBypassed()) {
                            args[0] = rewriteSessionSurfaces((List<?>) args[0]);
                        }
                        LogUtil.log("ã€CSã€‘æ‰§è¡Œäº† createConstrainedHighSpeedCaptureSession");
                        if (args[1] != null)
                            hookSessionCallback((CameraCaptureSession.StateCallback) args[1]);
                    }
                } catch (Throwable t) {
                    LogUtil.log("ã€CSã€‘createConstrainedHighSpeedCaptureSession before å¼‚å¸¸: " + t);
                }
                return chain.proceed(args);
            });
        } catch (Throwable t) {
            LogUtil.log("ã€CSã€‘Hook createConstrainedHighSpeedCaptureSession å¤±è´¥: " + t);
        }

        // 4. createReprocessableCaptureSession (API 23+)
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.M) {
            try {
                Method m = resolveMethodOnClass(deviceClass, "createReprocessableCaptureSession",
                        InputConfiguration.class, List.class,
                        CameraCaptureSession.StateCallback.class, Handler.class);
                Api101Runtime.requireModule().hook(m).intercept(chain -> {
                    Object[] args = toArgs(chain.getArgs());
                    try {
                        if (args[1] != null) {
                            if (HookGuards.shouldBypass(getCurrentPackageName(), HookGuards.getCurrentVideoFile())) {
                                yuvBridgeSessionReady = false;
                                return chain.proceed(args);
                            }
                            if (shouldBypassWhatsAppYuvSession((List<?>) args[1], getCurrentPackageName())) {
                                enableSessionBypass("createReprocessableCaptureSession");
                            } else {
                                disableSessionBypass();
                            }
                            if (!isCurrentSessionBypassed()) {
                                args[1] = rewriteSessionSurfaces((List<?>) args[1]);
                            }
                            LogUtil.log("ã€CSã€‘æ‰§è¡Œäº† createReprocessableCaptureSession ");
                            if (args[2] != null)
                                hookSessionCallback((CameraCaptureSession.StateCallback) args[2]);
                        }
                    } catch (Throwable t) {
                        LogUtil.log("ã€CSã€‘createReprocessableCaptureSession before å¼‚å¸¸: " + t);
                    }
                    return chain.proceed(args);
                });
            } catch (Throwable t) {
                LogUtil.log("ã€CSã€‘Hook createReprocessableCaptureSession å¤±è´¥: " + t);
            }
        }

        // 5. createReprocessableCaptureSessionByConfigurations (API 24+)
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.N) {
            try {
                Method m = resolveMethodOnClass(deviceClass,
                        "createReprocessableCaptureSessionByConfigurations",
                        InputConfiguration.class, List.class,
                        CameraCaptureSession.StateCallback.class, Handler.class);
                Api101Runtime.requireModule().hook(m).intercept(chain -> {
                    Object[] args = toArgs(chain.getArgs());
                    try {
                        if (args[1] != null) {
                            if (HookGuards.shouldBypass(getCurrentPackageName(), HookGuards.getCurrentVideoFile())) {
                                yuvBridgeSessionReady = false;
                                return chain.proceed(args);
                            }
                            if (shouldBypassWhatsAppYuvSession((List<?>) args[1], getCurrentPackageName())) {
                                enableSessionBypass("createReprocessableCaptureSessionByConfigurations");
                            } else {
                                disableSessionBypass();
                            }
                            if (!isCurrentSessionBypassed()) {
                                args[1] = rewriteOutputConfigurations((List<?>) args[1]);
                            }
                            LogUtil.log("ã€CSã€‘æ‰§è¡Œäº† createReprocessableCaptureSessionByConfigurations");
                            if (args[2] != null)
                                hookSessionCallback((CameraCaptureSession.StateCallback) args[2]);
                        }
                    } catch (Throwable t) {
                        LogUtil.log("ã€CSã€‘createReprocessableCaptureSessionByConfigurations before å¼‚å¸¸: " + t);
                    }
                    return chain.proceed(args);
                });
            } catch (Throwable t) {
                LogUtil.log("ã€CSã€‘Hook createReprocessableCaptureSessionByConfigurations å¤±è´¥: " + t);
            }
        }

        // 6. createCaptureSession(SessionConfiguration) (API 28+)
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.P) {
            try {
                Method m = resolveMethodOnClass(deviceClass, "createCaptureSession",
                        SessionConfiguration.class);
                Api101Runtime.requireModule().hook(m).intercept(chain -> {
                    Object[] args = toArgs(chain.getArgs());
                    try {
                        if (args[0] != null) {
                            if (HookGuards.shouldBypass(getCurrentPackageName(), HookGuards.getCurrentVideoFile())) {
                                yuvBridgeSessionReady = false;
                                return chain.proceed(args);
                            }
                            LogUtil.log("ã€CSã€‘æ‰§è¡Œäº† createCaptureSession (SessionConfiguration)");
                            realSessionConfig = (SessionConfiguration) args[0];
                            if (shouldBypassWhatsAppYuvSession(realSessionConfig.getOutputConfigurations(),
                                    getCurrentPackageName())) {
                                enableSessionBypass("createCaptureSession(SessionConfiguration)");
                            } else {
                                disableSessionBypass();
                            }
                            if (!isCurrentSessionBypassed()) {
                                fakeSessionConfig = rewriteSessionConfiguration(realSessionConfig);
                                args[0] = fakeSessionConfig;
                            }
                            hookSessionCallback(realSessionConfig.getStateCallback());
                        }
                    } catch (Throwable t) {
                        LogUtil.log("ã€CSã€‘createCaptureSession(SessionConfiguration) before å¼‚å¸¸: " + t);
                    }
                    return chain.proceed(args);
                });
            } catch (Throwable t) {
                LogUtil.log("ã€CSã€‘Hook createCaptureSession(SessionConfiguration) å¤±è´¥: " + t);
            }
        }
    }

    // =====================================================================
    // Session callback logging hooks
    // =====================================================================

    private void hookSessionCallback(CameraCaptureSession.StateCallback cb) {
        if (cb == null)
            return;
        if (!hookedSessionCallbackClasses.add(cb.getClass().getName())) {
            return;
        }
        Class<?> cbClass = cb.getClass();

        try {
            Method m = resolveMethodOnClass(cbClass, "onConfigureFailed", CameraCaptureSession.class);
            Api101Runtime.requireModule().hook(m).intercept(chain -> {
                Object[] args = toArgs(chain.getArgs());
                try {
                    LogUtil.log("ã€CSã€‘onConfigureFailed ï¼š" + args[0]);
                } catch (Throwable t) {
                    LogUtil.log("ã€CSã€‘onConfigureFailed before å¼‚å¸¸: " + t);
                }
                return chain.proceed(args);
            });
        } catch (Throwable t) {
            LogUtil.log("ã€CSã€‘Hook onConfigureFailed å¤±è´¥: " + t);
        }

        try {
            Method m = resolveMethodOnClass(cbClass, "onConfigured", CameraCaptureSession.class);
            Api101Runtime.requireModule().hook(m).intercept(chain -> {
                Object[] args = toArgs(chain.getArgs());
                try {
                    LogUtil.log("ã€CSã€‘onConfigured ï¼š" + args[0]);
                    markYuvBridgeSessionReadyIfPossible();
                } catch (Throwable t) {
                    LogUtil.log("ã€CSã€‘onConfigured before å¼‚å¸¸: " + t);
                }
                return chain.proceed(args);
            });
        } catch (Throwable t) {
            LogUtil.log("ã€CSã€‘Hook onConfigured å¤±è´¥: " + t);
        }

        try {
            Method m = resolveMethodOnClass(cbClass, "onClosed", CameraCaptureSession.class);
            Api101Runtime.requireModule().hook(m).intercept(chain -> {
                Object[] args = toArgs(chain.getArgs());
                try {
                    LogUtil.log("ã€CSã€‘onClosed ï¼š" + args[0]);
                } catch (Throwable t) {
                    LogUtil.log("ã€CSã€‘onClosed before å¼‚å¸¸: " + t);
                }
                return chain.proceed(args);
            });
        } catch (Throwable t) {
            LogUtil.log("ã€CSã€‘Hook session onClosed å¤±è´¥: " + t);
        }
    }

    public void releaseImageWriters() {
        releaseImageWriters(true);
    }

    private void releaseImageWriters(boolean clearTrackedReaders) {
        if (clearTrackedReaders) {
            isReleasing = true;
            stopAllWhatsAppYuvPumps();
        } else {
            stopAllWhatsAppYuvPumps();
        }
        for (ImageWriter writer : imageWriterMap.values()) {
            try {
                writer.close();
            } catch (Exception e) {
                LogUtil.log("ã€CSã€‘å…³é—­ ImageWriter å¤±è´¥: " + e);
            }
        }
        imageWriterMap.clear();
        pendingJpegSurfaces.clear();
        pendingPhotoSurface = null;
        bypassCurrentSession = false;
        closeFakeYuvBridges();
        internalFakeYuvReaderSurfaces.clear();
        cachedYuvFrameMap.clear();
        releaseCachedRetriever();
        lastYuvFrameWasFallback = true;
        if (clearTrackedReaders) {
            trackedReaderSurfaces.clear();
            surfaceFormatMap.clear();
            surfaceSizeMap.clear();
        }
        isReleasing = false;
    }

    public void updateImageReaderListener(Object imageReaderObj, Object listenerObj, Handler handler) {
        if (!(imageReaderObj instanceof ImageReader)) {
            return;
        }
        ImageReader imageReader = (ImageReader) imageReaderObj;
        Surface surface = imageReader.getSurface();
        if (!shouldKeepYuvReaderSurfaceForCurrentPackage(surface)
                || !shouldUseYuvPumpForSurface(surface)) {
            stopWhatsAppYuvPump(imageReader);
            return;
        }
        if (listenerObj == null) {
            stopWhatsAppYuvPump(imageReader);
            return;
        }
        ensureWhatsAppYuvPumpHandler();
        YuvCallbackPump pump = whatsappYuvPumpMap.get(imageReader);
        if (pump == null) {
            pump = new YuvCallbackPump(imageReader);
            whatsappYuvPumpMap.put(imageReader, pump);
        }
        pump.listener = listenerObj;
        pump.onImageAvailableMethod = null;
        pump.targetHandler = handler;
        if (pump.running || !shouldDriveYuvBridgeNow()) {
            return;
        }
        pump.running = true;
        whatsappYuvPumpHandler.post(pump.notifyRunnable);
        LogUtil.log("ã€CSã€‘YUV å›žè°ƒæ³µå·²å¯åŠ¨: " + surface);
    }

    private void startDeferredYuvPumpsIfReady() {
        if (!shouldDriveYuvBridgeNow()) {
            return;
        }
        ensureWhatsAppYuvPumpHandler();
        for (YuvCallbackPump pump : whatsappYuvPumpMap.values()) {
            if (pump == null || pump.listener == null || pump.running
                    || !shouldUseYuvPumpForSurface(pump.imageReader.getSurface())) {
                continue;
            }
            pump.running = true;
            whatsappYuvPumpHandler.post(pump.notifyRunnable);
            try {
                LogUtil.log("ã€CSã€‘YUV å›žè°ƒæ³µå·²å¯åŠ¨: " + pump.imageReader.getSurface());
            } catch (Throwable ignored) {
            }
        }
    }

    private void ensureWhatsAppYuvPumpHandler() {
        if (whatsappYuvPumpThread != null && whatsappYuvPumpHandler != null) {
            return;
        }
        whatsappYuvPumpThread = new HandlerThread("CS-WhatsAppYuvPump");
        whatsappYuvPumpThread.start();
        whatsappYuvPumpHandler = new Handler(whatsappYuvPumpThread.getLooper());
    }

    private void stopWhatsAppYuvPump(ImageReader imageReader) {
        if (imageReader == null) {
            return;
        }
        YuvCallbackPump pump = whatsappYuvPumpMap.remove(imageReader);
        if (pump == null) {
            return;
        }
        pump.running = false;
        Handler handler = whatsappYuvPumpHandler;
        if (handler != null) {
            handler.removeCallbacks(pump.notifyRunnable);
        }
    }

    private void stopAllWhatsAppYuvPumps() {
        Handler handler = whatsappYuvPumpHandler;
        if (handler != null) {
            for (YuvCallbackPump pump : whatsappYuvPumpMap.values()) {
                pump.running = false;
                handler.removeCallbacks(pump.notifyRunnable);
            }
        }
        whatsappYuvPumpMap.clear();
        if (whatsappYuvPumpThread != null) {
            try {
                whatsappYuvPumpThread.quitSafely();
            } catch (Throwable ignored) {
            }
            whatsappYuvPumpThread = null;
            whatsappYuvPumpHandler = null;
        }
    }

    /**
     * åœ¨æ³µçš„åŽå°çº¿ç¨‹ä¸Šé¢„åˆ·æ–° YUV ç¼“å­˜ã€‚
     * å°†é‡è®¡ç®—ï¼ˆGL æˆªå¸§ + RGBâ†’YUV è½¬æ¢ï¼‰ä»Ž WhatsApp çš„ handler çº¿ç¨‹ç§»åˆ°æ³µçº¿ç¨‹ï¼Œ
     * é¿å…é˜»å¡ž WhatsApp UI å¤„ç†å’ŒæŒ‚æ–­ä¿¡å·ã€‚
     */
    private void preRefreshYuvCache(YuvCallbackPump pump) {
        if (isReleasing || pump == null || !pump.running) {
            return;
        }
        if (!shouldDriveYuvBridgeNow()) {
            return;
        }
        try {
            Surface targetSurface = pump.imageReader.getSurface();
            if (targetSurface == null || !isCurrentSessionYuvReaderSurface(targetSurface)
                    || !shouldKeepYuvReaderSurfaceForCurrentPackage(targetSurface)
                    || !shouldUseYuvPumpForSurface(targetSurface)) {
                return;
            }
            int width = pump.imageReader.getWidth();
            int height = pump.imageReader.getHeight();
            if (width <= 0 || height <= 0) {
                int[] size = surfaceSizeMap.get(targetSurface);
                if (size != null && size.length >= 2) {
                    width = size[0];
                    height = size[1];
                }
            }
            if (width <= 0 || height <= 0) {
                return;
            }

            long now = SystemClock.elapsedRealtime();
            CachedYuvFrame cached = cachedYuvFrameMap.get(targetSurface);
            boolean needRefresh = false;
            if (cached == null || cached.width != width || cached.height != height) {
                cached = buildPlaceholderYuvFrame(width, height, now);
                cachedYuvFrameMap.put(targetSurface, cached);
                needRefresh = true;
            }
            long refreshInterval = lastYuvFrameWasFallback
                    ? YUV_CACHE_REFRESH_FALLBACK_MS
                    : YUV_CACHE_REFRESH_GL_MS;
            if (cached.isPlaceholder || now - cached.generatedAtMs >= refreshInterval || needRefresh) {
                CachedYuvFrame refreshed = buildCachedYuvFrame(targetSurface, width, height, now);
                if (refreshed != null) {
                    cachedYuvFrameMap.put(targetSurface, refreshed);
                }
            }
        } catch (Throwable t) {
            LogUtil.log("ã€CSã€‘é¢„åˆ·æ–° YUV ç¼“å­˜å¼‚å¸¸: " + t);
        }
    }

    private void dispatchWhatsAppYuvCallback(YuvCallbackPump pump) {
        if (pump == null || !pump.running || pump.listener == null || isReleasing) {
            return;
        }
        if (!shouldDriveYuvBridgeNow()) {
            return;
        }
        Runnable callback = new Runnable() {
            @Override
            public void run() {
                try {
                    if (pump.listener instanceof OnImageAvailableListener) {
                        ((OnImageAvailableListener) pump.listener).onImageAvailable(pump.imageReader);
                    } else {
                        pump.resolveOnImageAvailableMethod().invoke(pump.listener, pump.imageReader);
                    }
                } catch (Throwable t) {
                    pump.running = false;
                    LogUtil.log("ã€CSã€‘YUV å›žè°ƒåˆ†å‘å¤±è´¥: " + t);
                }
            }
        };
        if (pump.targetHandler != null) {
            pump.targetHandler.post(callback);
        } else {
            callback.run();
        }
    }

    public Image acquireFakeWhatsAppYuvImage(Object imageReader, Surface targetSurface) {
        if (isReleasing || targetSurface == null || !shouldKeepYuvReaderSurfaceForCurrentPackage(targetSurface)
                || !isCurrentSessionYuvReaderSurface(targetSurface)
                || !isYuvReaderSurface(targetSurface)
                || !shouldDriveYuvBridgeNow()) {
            return null;
        }
        int width = 0;
        int height = 0;
        if (imageReader != null) {
            try {
                ImageReader typedReader = (ImageReader) imageReader;
                width = typedReader.getWidth();
                height = typedReader.getHeight();
            } catch (Throwable ignored) {
            }
        }
        if (width <= 0 || height <= 0) {
            int[] size = surfaceSizeMap.get(targetSurface);
            if (size != null && size.length >= 2) {
                width = size[0];
                height = size[1];
            }
        }
        if (width <= 0 || height <= 0) {
            return null;
        }

        // ç¼“å­˜ç”±æ³µçº¿ç¨‹ preRefreshYuvCache é¢„å…ˆåˆ·æ–°ï¼Œè¿™é‡Œåªè¯»å–
        CachedYuvFrame cached = cachedYuvFrameMap.get(targetSurface);
        long now = SystemClock.elapsedRealtime();
        long refreshInterval = lastYuvFrameWasFallback
                ? YUV_CACHE_REFRESH_FALLBACK_MS
                : YUV_CACHE_REFRESH_GL_MS;
        boolean needRefresh = cached == null
                || cached.width != width
                || cached.height != height
                || cached.isPlaceholder
                || now - cached.generatedAtMs >= refreshInterval;
        if (needRefresh) {
            CachedYuvFrame refreshed = buildCachedYuvFrame(targetSurface, width, height, now);
            if (refreshed != null) {
                cached = refreshed;
                cachedYuvFrameMap.put(targetSurface, refreshed);
            } else if (cached == null || cached.width != width || cached.height != height) {
                cached = buildPlaceholderYuvFrame(width, height, now);
                cachedYuvFrameMap.put(targetSurface, cached);
            }
        }
        if (cached == null) {
            return null;
        }
        try {
            FakeYuvBridge bridge = getOrCreateFakeYuvBridge(targetSurface, width, height);
            if (bridge == null) {
                return null;
            }
            enterFakeYuvAcquire();
            try {
                clearPendingFakeYuvBridgeImages(bridge);
                Image inputImage = bridge.writer.dequeueInputImage();
                if (inputImage == null) {
                    return null;
                }
                boolean queued = false;
                try {
                    copyCachedYuvFrameToImage(cached, inputImage);
                    inputImage.setCropRect(new Rect(0, 0, width, height));
                    inputImage.setTimestamp(System.nanoTime());
                    bridge.writer.queueInputImage(inputImage);
                    queued = true;
                } finally {
                    if (!queued) {
                        inputImage.close();
                    }
                }
                // ä½¿ç”¨ acquireNextImage è€Œéž acquireLatestImageï¼š
                // acquireLatestImage ä¼šè‡ªåŠ¨ close æ‰€æœ‰ä¹‹å‰å·² acquire ä½†æœªè¢«æ¶ˆè´¹æ–¹ close çš„ Imageï¼Œ
                // WhatsApp VoipCameraManager.getLastCachedFrame() ä¼šç¼“å­˜æ—§ Image å¼•ç”¨ï¼Œ
                // å¦‚æžœæˆ‘ä»¬é€šè¿‡ acquireLatestImage éšå¼å…³é—­äº†å®ƒï¼ŒWhatsApp åœ¨åŽç»­è°ƒç”¨
                // image.getPlanes() æ—¶å°±ä¼šæŠ›å‡º IllegalStateException: Image is already closed
                Image image = bridge.reader.acquireNextImage();
                if (image != null) {
                    if (cached.isPlaceholder) {
                        maybeLogWhatsAppYuvPlaceholder(width, height);
                    }
                    maybeLogWhatsAppYuvSuccess(width, height, image.getTimestamp());
                }
                return image;
            } finally {
                exitFakeYuvAcquire();
            }
        } catch (Exception e) {
            LogUtil.log("ã€CSã€‘YUV ä¼ªå¸§èŽ·å–å¤±è´¥: " + e);
            return null;
        }
    }

    private void clearPendingFakeYuvBridgeImages(FakeYuvBridge bridge) {
        if (bridge == null) {
            return;
        }
        while (true) {
            Image pendingImage = null;
            try {
                pendingImage = bridge.reader.acquireNextImage();
            } catch (IllegalStateException e) {
                break;
            } catch (Exception e) {
                LogUtil.log("ã€CSã€‘æ¸…ç† YUV æ¡¥æ—§å¸§å¤±è´¥: " + e);
                break;
            }
            if (pendingImage == null) {
                break;
            }
            try {
                pendingImage.close();
            } catch (Exception ignored) {
            }
        }
    }

    private CachedYuvFrame buildCachedYuvFrame(Surface targetSurface, int width, int height, long nowMs) {
        Bitmap frame = captureFrameForYuv(width, height);
        if (frame == null) {
            return null;
        }
        try {
            if (frame.getWidth() != width || frame.getHeight() != height) {
                Bitmap scaled = fitBitmapToTargetAspect(frame, width, height);
                if (scaled != frame) {
                    frame.recycle();
                    frame = scaled;
                }
            }
            int[] pixels = new int[width * height];
            frame.getPixels(pixels, 0, width, 0, 0, width, height);

            byte[] yPlane = new byte[width * height];
            int chromaWidth = width / 2;
            int chromaHeight = height / 2;
            byte[] uPlane = new byte[chromaWidth * chromaHeight];
            byte[] vPlane = new byte[chromaWidth * chromaHeight];

            // å•æ¬¡éåŽ†ï¼šåŒæ—¶è®¡ç®— Yï¼ˆå…¨åƒç´ ï¼‰å’Œ UVï¼ˆå¶æ•°è¡Œå¶æ•°åˆ—é‡‡æ ·ï¼‰
            // ç›¸æ¯”åŽŸæ¥çš„åŒå¾ªçŽ¯ + computeAverageUv æ–¹æ³•è°ƒç”¨ï¼ˆæ¯å¸§ ~23ä¸‡æ¬¡æ–¹æ³•è°ƒç”¨å’Œæ•°ç»„åˆ†é…ï¼‰ï¼Œ
            // å¤§å¹…å‡å°‘å¼€é”€
            for (int row = 0; row < height; row++) {
                int rowOffset = row * width;
                boolean isEvenRow = (row & 1) == 0;
                int chromaRowBase = isEvenRow ? (row >> 1) * chromaWidth : -1;

                for (int col = 0; col < width; col++) {
                    int pixel = pixels[rowOffset + col];
                    int r = (pixel >> 16) & 0xff;
                    int g = (pixel >> 8) & 0xff;
                    int b = pixel & 0xff;

                    // Y
                    int yVal = ((66 * r + 129 * g + 25 * b + 128) >> 8) + 16;
                    yPlane[rowOffset + col] = (byte) (yVal < 0 ? 0 : (yVal > 255 ? 255 : yVal));

                    // UVï¼šä»…åœ¨å¶æ•°è¡Œå¶æ•°åˆ—é‡‡æ ·ï¼ˆæ¯ 2x2 å—å·¦ä¸Šè§’åƒç´ ï¼‰
                    if (isEvenRow && (col & 1) == 0) {
                        int uVal = ((-38 * r - 74 * g + 112 * b + 128) >> 8) + 128;
                        int vVal = ((112 * r - 94 * g - 18 * b + 128) >> 8) + 128;
                        int chromaIdx = chromaRowBase + (col >> 1);
                        uPlane[chromaIdx] = (byte) (uVal < 0 ? 0 : (uVal > 255 ? 255 : uVal));
                        vPlane[chromaIdx] = (byte) (vVal < 0 ? 0 : (vVal > 255 ? 255 : vVal));
                    }
                }
            }

            return new CachedYuvFrame(width, height, yPlane, uPlane, vPlane, nowMs, System.nanoTime(), false);
        } finally {
            frame.recycle();
        }
    }

    private CachedYuvFrame buildPlaceholderYuvFrame(int width, int height, long nowMs) {
        byte[] yPlane = new byte[width * height];
        byte[] uPlane = new byte[(width / 2) * (height / 2)];
        byte[] vPlane = new byte[(width / 2) * (height / 2)];
        Arrays.fill(yPlane, (byte) 16);
        Arrays.fill(uPlane, (byte) 128);
        Arrays.fill(vPlane, (byte) 128);
        return new CachedYuvFrame(width, height, yPlane, uPlane, vPlane, nowMs, System.nanoTime(), true);
    }

    private void copyCachedYuvFrameToImage(CachedYuvFrame cached, Image image) {
        if (image == null || image.getPlanes() == null || image.getPlanes().length < 3) {
            throw new IllegalStateException("YUV Image plane ä¸å¯ç”¨");
        }
        Image.Plane[] planes = image.getPlanes();
        ByteBuffer yBuffer = planes[0].getBuffer();
        ByteBuffer uBuffer = planes[1].getBuffer();
        ByteBuffer vBuffer = planes[2].getBuffer();
        if (yBuffer == null || uBuffer == null || vBuffer == null
                || yBuffer.isReadOnly() || uBuffer.isReadOnly() || vBuffer.isReadOnly()) {
            throw new IllegalStateException("YUV Image plane Buffer ä¸å¯å†™");
        }

        int width = image.getWidth();
        int height = image.getHeight();
        if (width <= 0 || height <= 0 || width != cached.width || height != cached.height) {
            throw new IllegalStateException("YUV Image å°ºå¯¸ä¸åŒ¹é…");
        }

        yBuffer.clear();
        uBuffer.clear();
        vBuffer.clear();

        int yRowStride = planes[0].getRowStride();
        int yPixelStride = planes[0].getPixelStride();
        int uRowStride = planes[1].getRowStride();
        int uPixelStride = planes[1].getPixelStride();
        int vRowStride = planes[2].getRowStride();
        int vPixelStride = planes[2].getPixelStride();

        for (int y = 0; y < height; y++) {
            int yRowOffset = y * yRowStride;
            int sourceRowOffset = y * width;
            for (int x = 0; x < width; x++) {
                yBuffer.put(yRowOffset + x * yPixelStride, cached.yPlane[sourceRowOffset + x]);
            }
        }

        int chromaWidth = width / 2;
        int chromaHeight = height / 2;
        for (int y = 0; y < chromaHeight; y++) {
            int uRowOffset = y * uRowStride;
            int vRowOffset = y * vRowStride;
            int sourceRowOffset = y * chromaWidth;
            for (int x = 0; x < chromaWidth; x++) {
                uBuffer.put(uRowOffset + x * uPixelStride, cached.uPlane[sourceRowOffset + x]);
                vBuffer.put(vRowOffset + x * vPixelStride, cached.vPlane[sourceRowOffset + x]);
            }
        }
    }

    private FakeYuvBridge getOrCreateFakeYuvBridge(Surface targetSurface, int width, int height) {
        FakeYuvBridge bridge = fakeYuvBridgeMap.get(targetSurface);
        if (bridge != null && bridge.width == width && bridge.height == height) {
            return bridge;
        }
        if (bridge != null) {
            closeFakeYuvBridge(bridge);
        }
        try {
            enterInternalBridgeCreation();
            ImageReader reader = null;
            try {
                // maxImages è®¾ä¸º 8ï¼šéœ€è¦è¶³å¤Ÿå¤§ä»¥å®¹çº³ WhatsApp ç¼“å­˜çš„æ—§å¸§ + å½“å‰å¸§ + writer é˜Ÿåˆ—
                // å¦‚æžœå¤ªå°ï¼ŒWhatsApp æŒæœ‰æ—§ Image å¼•ç”¨æ—¶æ–°å¸§å°±æ— æ³•è¢« acquire
                reader = ImageReader.newInstance(width, height, ImageFormat.YUV_420_888,
                        WHATSAPP_YUV_BRIDGE_MAX_IMAGES);
            } finally {
                exitInternalBridgeCreation();
            }
            ImageWriter writer = ImageWriter.newInstance(reader.getSurface(), WHATSAPP_YUV_BRIDGE_MAX_IMAGES);
            internalFakeYuvReaderSurfaces.add(reader.getSurface());
            bridge = new FakeYuvBridge(reader, writer, width, height);
            fakeYuvBridgeMap.put(targetSurface, bridge);
            return bridge;
        } catch (Exception e) {
            LogUtil.log("ã€CSã€‘åˆ›å»º YUV æ¡¥å¤±è´¥: " + e);
            return null;
        }
    }

    private void closeFakeYuvBridges() {
        for (FakeYuvBridge bridge : fakeYuvBridgeMap.values()) {
            closeFakeYuvBridge(bridge);
        }
        fakeYuvBridgeMap.clear();
    }

    private void closeFakeYuvBridge(FakeYuvBridge bridge) {
        if (bridge == null) {
            return;
        }
        try {
            internalFakeYuvReaderSurfaces.remove(bridge.reader.getSurface());
        } catch (Exception ignored) {
        }
        // å»¶è¿Ÿå…³é—­ bridge çš„ reader/writerï¼š
        // WhatsApp å¯èƒ½ä»æŒæœ‰ä¹‹å‰é€šè¿‡ acquireNextImage() èŽ·å–çš„ Image å¼•ç”¨ï¼Œ
        // å¦‚æžœç«‹åˆ» close readerï¼Œè¿™äº› Image ä¼šå˜ä¸º invalidï¼ŒWhatsApp è°ƒç”¨
        // getPlanes() æ—¶å°±ä¼šæŠ›å‡º IllegalStateException: Image is already closedã€‚
        // å»¶è¿Ÿ 500ms è®© WhatsApp æœ‰æ—¶é—´æ¶ˆè´¹å¹¶ close æ—§ Imageã€‚
        final ImageWriter w = bridge.writer;
        final ImageReader r = bridge.reader;
        new Thread(new Runnable() {
            @Override
            public void run() {
                try {
                    Thread.sleep(500L);
                } catch (InterruptedException ignored) {
                }
                try {
                    w.close();
                } catch (Exception ignored) {
                }
                try {
                    r.close();
                } catch (Exception ignored) {
                }
            }
        }, "CS-BridgeClose").start();
    }

    private void maybeLogWhatsAppYuvSuccess(int width, int height, long timestampNs) {
        long now = SystemClock.elapsedRealtime();
        yuvFrameCount++;
        // æ¯ 5 ç§’è¾“å‡ºä¸€æ¬¡å®žé™…å¸§çŽ‡
        if (yuvFpsWindowStartMs == 0L) {
            yuvFpsWindowStartMs = now;
            yuvFrameCount = 1;
        } else if (now - yuvFpsWindowStartMs >= 5000L) {
            float fps = yuvFrameCount * 1000f / (now - yuvFpsWindowStartMs);
            LogUtil.log("ã€CSã€‘YUV å®žé™…å¸§çŽ‡: " + String.format(Locale.US, "%.1f", fps)
                    + " fps (" + yuvFrameCount + " frames / 5s)"
                    + (lastYuvFrameWasFallback ? " [fallback]" : " [GL]"));
            yuvFrameCount = 0;
            yuvFpsWindowStartMs = now;
        }
        if (now - lastWhatsAppYuvSuccessLogMs < 1000L) {
            return;
        }
        lastWhatsAppYuvSuccessLogMs = now;
        LogUtil.log("ã€CSã€‘YUV ä¼ªå¸§å·²ç”Ÿæˆ: " + width + "x" + height + " ts=" + timestampNs);
    }

    private void maybeLogWhatsAppYuvPlaceholder(int width, int height) {
        long now = SystemClock.elapsedRealtime();
        if (now - lastWhatsAppYuvPlaceholderLogMs < 1000L) {
            return;
        }
        lastWhatsAppYuvPlaceholderLogMs = now;
        LogUtil.log("ã€CSã€‘YUV ä½¿ç”¨å ä½å¸§å¯åŠ¨: " + width + "x" + height);
    }

    private void maybeLogNoGlRendererFallback() {
        long now = SystemClock.elapsedRealtime();
        if (now - lastNoGlRendererLogMs < 1000L) {
            return;
        }
        lastNoGlRendererLogMs = now;
        LogUtil.log("ã€CSã€‘æ— å¯ç”¨ GL æ¸²æŸ“å™¨ï¼Œå›žé€€åˆ°è§†é¢‘æ–‡ä»¶æˆªå¸§");
    }

    private void maybeLogGlNullFallback() {
        long now = SystemClock.elapsedRealtime();
        if (now - lastGlNullFallbackLogMs < 1000L) {
            return;
        }
        lastGlNullFallbackLogMs = now;
        LogUtil.log("ã€CSã€‘GL æˆªå¸§è¿”å›ž nullï¼Œå›žé€€åˆ°è§†é¢‘æ–‡ä»¶æˆªå¸§");
    }

    private void maybeLogGlBlackFallback() {
        long now = SystemClock.elapsedRealtime();
        if (now - lastGlBlackFallbackLogMs < 1000L) {
            return;
        }
        lastGlBlackFallbackLogMs = now;
        LogUtil.log("ã€CSã€‘GL æˆªå¸§è¿‡é»‘ï¼Œå›žé€€åˆ°è§†é¢‘æ–‡ä»¶æˆªå¸§");
    }

    private static final class CachedYuvFrame {
        final int width;
        final int height;
        final byte[] yPlane;
        final byte[] uPlane;
        final byte[] vPlane;
        final long generatedAtMs;
        final long timestampNs;
        final boolean isPlaceholder;

        CachedYuvFrame(int width, int height, byte[] yPlane, byte[] uPlane, byte[] vPlane,
                long generatedAtMs, long timestampNs, boolean isPlaceholder) {
            this.width = width;
            this.height = height;
            this.yPlane = yPlane;
            this.uPlane = uPlane;
            this.vPlane = vPlane;
            this.generatedAtMs = generatedAtMs;
            this.timestampNs = timestampNs;
            this.isPlaceholder = isPlaceholder;
        }
    }

    private static final class FakeYuvBridge {
        final ImageReader reader;
        final ImageWriter writer;
        final int width;
        final int height;

        FakeYuvBridge(ImageReader reader, ImageWriter writer, int width, int height) {
            this.reader = reader;
            this.writer = writer;
            this.width = width;
            this.height = height;
        }
    }

    private final class YuvCallbackPump {
        final ImageReader imageReader;
        volatile Object listener;
        volatile Handler targetHandler;
        volatile boolean running;
        volatile Method onImageAvailableMethod;
        final Runnable notifyRunnable = new Runnable() {
            @Override
            public void run() {
                if (!running || whatsappYuvPumpHandler == null) {
                    return;
                }
                long startMs = SystemClock.elapsedRealtime();
                // åœ¨æ³µçº¿ç¨‹ä¸Šé¢„åˆ·æ–° YUV ç¼“å­˜ï¼ˆé‡è®¡ç®—ï¼‰ï¼Œä¸é˜»å¡ž WhatsApp çš„ handler
                preRefreshYuvCache(YuvCallbackPump.this);
                // åˆ†å‘è½»é‡å›žè°ƒåˆ° WhatsApp handlerï¼ˆä»…è¯»å–ç¼“å­˜ï¼‰
                dispatchWhatsAppYuvCallback(YuvCallbackPump.this);
                long elapsed = SystemClock.elapsedRealtime() - startMs;
                long delay = Math.max(10L, 66L - elapsed);
                whatsappYuvPumpHandler.postDelayed(this, delay);
            }
        };

        YuvCallbackPump(ImageReader imageReader) {
            this.imageReader = imageReader;
        }

        Method resolveOnImageAvailableMethod() throws NoSuchMethodException {
            Method method = onImageAvailableMethod;
            if (method != null) {
                return method;
            }
            Object currentListener = listener;
            if (currentListener == null) {
                throw new NoSuchMethodException("Listener missing");
            }
            method = currentListener.getClass().getMethod("onImageAvailable", ImageReader.class);
            method.setAccessible(true);
            onImageAvailableMethod = method;
            return method;
        }
    }

    /** èŽ·å–å½“å‰æ´»è·ƒçš„ GLVideoRendererï¼ˆä¼˜å…ˆ previewï¼Œå…¶æ¬¡ readerï¼‰ */
    public GLVideoRenderer getActiveRenderer() {
        MediaPlayerManager pm = HookMain.playerManager;
        if (pm.c2_renderer != null && pm.c2_renderer.isInitialized())
            return pm.c2_renderer;
        if (pm.c2_renderer_1 != null && pm.c2_renderer_1.isInitialized())
            return pm.c2_renderer_1;
        if (pm.c2_reader_renderer != null && pm.c2_reader_renderer.isInitialized())
            return pm.c2_reader_renderer;
        if (pm.c2_reader_renderer_1 != null && pm.c2_reader_renderer_1.isInitialized())
            return pm.c2_reader_renderer_1;
        return null;
    }

    private GLVideoRenderer getPreferredYuvRenderer() {
        MediaPlayerManager pm = HookMain.playerManager;
        if (pm.c2_renderer != null && pm.c2_renderer.isInitialized()) {
            return pm.c2_renderer;
        }
        if (pm.c2_renderer_1 != null && pm.c2_renderer_1.isInitialized()) {
            return pm.c2_renderer_1;
        }
        return getActiveRenderer();
    }

    private void markYuvBridgeSessionReadyIfPossible() {
        yuvBridgeSessionReady = getActiveRenderer() != null || VideoManager.hasUsableMediaSource();
        if (yuvBridgeSessionReady) {
            startDeferredYuvPumpsIfReady();
        }
    }

    /**
     * FIXED: Now uses captureFrameForYuv() instead of captureFrameForStill()
     * This ensures the video file fallback path is used when the GL renderer fails
     * on MediaTek HAL 3.6 devices, fixing the YV12:0|HW_TEXTURE buffer error.
     */
    private byte[] createFakeJpegBytes(Surface targetSurface, int maxBytes) {
        int targetWidth = HookMain.c2_ori_width;
        int targetHeight = HookMain.c2_ori_height;
        int[] size = surfaceSizeMap.get(targetSurface);
        if (size != null && size.length >= 2) {
            targetWidth = size[0];
            targetHeight = size[1];
        }
        if (targetWidth <= 0 || targetHeight <= 0) {
            targetWidth = 1280;
            targetHeight = 720;
        }

        // FIX: Use captureFrameForYuv() which has the video file fallback path
        // This works on MediaTek HAL where captureFrameForStill() fails with YV12/HW_TEXTURE error
        Bitmap frame = captureFrameForYuv(targetWidth, targetHeight);
        if (frame == null) {
            LogUtil.log("ã€CSã€‘æ— æ³•èŽ·å–å¯ç”¨é™æ€å¸§");
            return null;
        }

        return compressBitmapToJpeg(frame, maxBytes);
    }

    /**
     * æˆªå–å½“å‰å¸§ï¼ˆä½¿ç”¨æ¸²æŸ“å™¨å½“å‰æ—‹è½¬ï¼‰ï¼Œç”¨äºŽ JPEG æ‹ç…§æ›¿æ¢ã€‚
     */
    private Bitmap captureFrameForStill(int targetWidth, int targetHeight) {
        return captureFrameInternal(targetWidth, targetHeight, -1);
    }

    /**
     * æˆªå–å½“å‰å¸§å¹¶å¼ºåˆ¶åº”ç”¨ video_rotation_offset æ—‹è½¬ï¼Œç”¨äºŽ WhatsApp YUV å¸§ç”Ÿæˆã€‚
     * é¢„è§ˆæ¸²æŸ“å™¨æ—‹è½¬è®¾ä¸º 0Â°ï¼ˆæœ¬æœºè‡ªæ‹ç”»é¢æ–¹å‘æ­£ç¡®ï¼‰ï¼Œ
     * ä½† YUV å¸§éœ€è¦ video_rotation_offset æ—‹è½¬æ‰èƒ½è®©å¯¹æ–¹çœ‹åˆ°æ­£ç¡®æ–¹å‘ã€‚
     */
    private Bitmap captureFrameForYuv(int targetWidth, int targetHeight) {
        int rotation = VideoManager.getConfig().getInt(ConfigManager.KEY_VIDEO_ROTATION_OFFSET, 0);
        return captureFrameInternal(targetWidth, targetHeight, rotation);
    }

    /**
     * @param rotationOverride -1=ä½¿ç”¨æ¸²æŸ“å™¨å½“å‰æ—‹è½¬, >=0=ä¸´æ—¶è¦†ç›–æŒ‡å®šè§’åº¦
     */
    private Bitmap captureFrameInternal(int targetWidth, int targetHeight, int rotationOverride) {
        if (isReleasing) {
            return null;
        }
        if (!VideoManager.hasUsableMediaSource()) {
            lastYuvFrameWasFallback = true;
            return null;
        }
        GLVideoRenderer activeRenderer = getPreferredYuvRenderer();
        if (activeRenderer != null) {
            int captureWidth = activeRenderer.getSurfaceWidth();
            int captureHeight = activeRenderer.getSurfaceHeight();
            if (captureWidth <= 0 || captureHeight <= 0) {
                captureWidth = targetWidth;
                captureHeight = targetHeight;
            }

            Bitmap frame = activeRenderer.captureFrameWithRotation(
                    captureWidth, captureHeight, rotationOverride);
            if (frame != null) {
                frame = fitBitmapToTargetAspect(frame, targetWidth, targetHeight);
                if (!isBitmapMostlyBlack(frame)) {
                    lastYuvFrameWasFallback = false;
                    return frame;
                }
                maybeLogGlBlackFallback();
                frame.recycle();
            } else {
                maybeLogGlNullFallback();
            }
        } else {
            maybeLogNoGlRendererFallback();
        }

        lastYuvFrameWasFallback = true;

        return captureFrameFromVideoFile(targetWidth, targetHeight);
    }

    /** ç¼“å­˜çš„ MediaMetadataRetriever å®žä¾‹ï¼Œé¿å…æ¯å¸§éƒ½é‡æ–°åˆ›å»ºå’Œ setDataSource */
    private MediaMetadataRetriever cachedRetriever;
    private String cachedRetrieverPath;

    private Bitmap captureFrameFromVideoFile(int targetWidth, int targetHeight) {
        // Stream mode: MediaMetadataRetriever cannot work with network URLs.
        // Return null to let caller use GL capture or last-frame cache.
        if (VideoManager.isStreamMode()) {
            LogUtil.log("ã€CSã€‘æµæ¨¡å¼ä¸‹è·³è¿‡ MediaMetadataRetriever æˆªå¸§");
            return null;
        }
        try {
            String currentPath = VideoManager.getCurrentVideoPath();
            // å¤ç”¨å·²æœ‰ retrieverï¼Œåªåœ¨è·¯å¾„å˜åŒ–æ—¶é‡æ–°åˆ›å»º
            if (cachedRetriever == null || cachedRetrieverPath == null
                    || !cachedRetrieverPath.equals(currentPath)) {
                releaseCachedRetriever();
                MediaMetadataRetriever retriever = new MediaMetadataRetriever();
                android.os.ParcelFileDescriptor pfd = VideoManager.getVideoPFD();
                if (pfd != null) {
                    try {
                        retriever.setDataSource(pfd.getFileDescriptor());
                    } finally {
                        try {
                            pfd.close();
                        } catch (Exception ignored) {
                        }
                    }
                } else {
                    retriever.setDataSource(currentPath);
                }
                cachedRetriever = retriever;
                cachedRetrieverPath = currentPath;
            }

            long positionUs = HookMain.playerManager.getCamera2PlaybackPositionMs() * 1000L;
            if (positionUs <= 0) {
                positionUs = 33_000L;
            }
            // ä½¿ç”¨ OPTION_CLOSEST_SYNC è€Œéž OPTION_CLOSESTï¼š
            // OPTION_CLOSEST éœ€è¦ç²¾ç¡® seek åˆ°æŒ‡å®šæ—¶é—´æˆ³å¹¶è§£ç åˆ°è¯¥å¸§ï¼Œéžå¸¸æ…¢ï¼ˆ~500-800msï¼‰ï¼›
            // OPTION_CLOSEST_SYNC åª seek åˆ°æœ€è¿‘çš„å…³é”®å¸§ï¼Œé€šå¸¸ <100msï¼Œ
            // å¯¹äºŽé¢„è§ˆç›®çš„è¶³å¤Ÿç”¨ï¼Œç‰ºç‰²ç²¾åº¦æ¢å–å¸§çŽ‡ã€‚
            Bitmap frame = cachedRetriever.getFrameAtTime(positionUs,
                    MediaMetadataRetriever.OPTION_CLOSEST_SYNC);
            if (frame == null && positionUs > 0) {
                frame = cachedRetriever.getFrameAtTime(-1,
                        MediaMetadataRetriever.OPTION_CLOSEST_SYNC);
            }
            if (frame == null) {
                return null;
            }
            return fitBitmapToTargetAspect(frame, targetWidth, targetHeight);
        } catch (Exception e) {
            LogUtil.log("ã€CSã€‘è§†é¢‘æ–‡ä»¶æˆªå¸§å¤±è´¥: " + e);
            // å‡ºé”™æ—¶é‡Šæ”¾ç¼“å­˜çš„ retrieverï¼Œä¸‹æ¬¡é‡è¯•
            releaseCachedRetriever();
            return null;
        }
    }

    private void releaseCachedRetriever() {
        if (cachedRetriever != null) {
            try {
                cachedRetriever.release();
            } catch (Exception ignored) {
            }
            cachedRetriever = null;
            cachedRetrieverPath = null;
        }
    }

    private Bitmap fitBitmapToTargetAspect(Bitmap source, int targetWidth, int targetHeight) {
        if (source == null) {
            return null;
        }
        if (targetWidth <= 0 || targetHeight <= 0) {
            return source;
        }

        int sourceWidth = source.getWidth();
        int sourceHeight = source.getHeight();
        if (sourceWidth <= 0 || sourceHeight <= 0) {
            return source;
        }

        float sourceAspect = (float) sourceWidth / (float) sourceHeight;
        float targetAspect = (float) targetWidth / (float) targetHeight;

        Rect cropRect;
        if (Math.abs(sourceAspect - targetAspect) < 0.001f) {
            cropRect = new Rect(0, 0, sourceWidth, sourceHeight);
        } else if (sourceAspect > targetAspect) {
            int croppedWidth = Math.max(1, Math.round(sourceHeight * targetAspect));
            int left = Math.max(0, (sourceWidth - croppedWidth) / 2);
            cropRect = new Rect(left, 0, Math.min(sourceWidth, left + croppedWidth), sourceHeight);
        } else {
            int croppedHeight = Math.max(1, Math.round(sourceWidth / targetAspect));
            int top = Math.max(0, (sourceHeight - croppedHeight) / 2);
            cropRect = new Rect(0, top, sourceWidth, Math.min(sourceHeight, top + croppedHeight));
        }

        Bitmap cropped = source;
        if (cropRect.left != 0 || cropRect.top != 0 || cropRect.width() != sourceWidth
                || cropRect.height() != sourceHeight) {
            cropped = Bitmap.createBitmap(source, cropRect.left, cropRect.top, cropRect.width(), cropRect.height());
            source.recycle();
        }

        if (cropped.getWidth() == targetWidth && cropped.getHeight() == targetHeight) {
            return cropped;
        }

        Bitmap scaled = Bitmap.createScaledBitmap(cropped, targetWidth, targetHeight, true);
        if (scaled != cropped) {
            cropped.recycle();
        }
        return scaled;
    }

    private byte[] compressBitmapToJpeg(Bitmap frame, int maxBytes) {
        if (frame == null) {
            return null;
        }

        int[] qualities = { 92, 80, 65, 50 };
        ByteArrayOutputStream baos = new ByteArrayOutputStream();
        byte[] jpegBytes = null;
        try {
            for (int quality : qualities) {
                baos.reset();
                frame.compress(Bitmap.CompressFormat.JPEG, quality, baos);
                byte[] candidate = baos.toByteArray();
                if (maxBytes <= 0 || candidate.length <= maxBytes) {
                    jpegBytes = candidate;
                    break;
                }
            }
        } finally {
            frame.recycle();
        }

        if (jpegBytes == null) {
            LogUtil.log("ã€CSã€‘ç…§ç‰‡åŽ‹ç¼©åŽä¾ç„¶å¤§äºŽ Buffer å®¹é‡: " + maxBytes);
        }
        return jpegBytes;
    }

    private boolean isBitmapMostlyBlack(Bitmap bitmap) {
        if (bitmap == null) {
            return true;
        }
        int width = bitmap.getWidth();
        int height = bitmap.getHeight();
        if (width <= 0 || height <= 0) {
            return true;
        }
        int stepX = Math.max(1, width / 8);
        int stepY = Math.max(1, height / 8);
        int samples = 0;
        int darkSamples = 0;
        for (int y = stepY / 2; y < height; y += stepY) {
            for (int x = stepX / 2; x < width; x += stepX) {
                int pixel = bitmap.getPixel(x, y);
                int r = (pixel >> 16) & 0xff;
                int g = (pixel >> 8) & 0xff;
                int b = pixel & 0xff;
                int brightness = (r + g + b) / 3;
                samples++;
                if (brightness < 16) {
                    darkSamples++;
                }
            }
        }
        return samples == 0 || darkSamples * 100 / samples >= 85;
    }

    public boolean replaceJpegImageIfNeeded(Object imageReader, Image image) {
        if (imageReader == null || image == null) {
            return false;
        }
        try {
            Surface surface = ((ImageReader) imageReader).getSurface();
            if (!shouldKeepRealReaderSurface(surface) || !pendingJpegSurfaces.contains(surface)) {
                return false;
            }
            if (image.getPlanes() == null || image.getPlanes().length == 0) {
                LogUtil.log("ã€CSã€‘JPEG Image æ— å¯å†™ Planeï¼Œæ”¾å¼ƒæ›¿æ¢");
                return false;
            }
            ByteBuffer buffer = image.getPlanes()[0].getBuffer();
            if (buffer == null) {
                LogUtil.log("ã€CSã€‘JPEG Plane Buffer ä¸º nullï¼Œæ”¾å¼ƒæ›¿æ¢");
                return false;
            }
            if (buffer.isReadOnly()) {
                LogUtil.log("ã€CSã€‘JPEG Plane Buffer åªè¯»ï¼Œæ”¾å¼ƒæ›¿æ¢");
                return false;
            }

            byte[] jpegBytes = createFakeJpegBytes(surface, buffer.capacity());
            if (jpegBytes == null || jpegBytes.length == 0) {
                return false;
            }

            buffer.clear();
            buffer.put(jpegBytes);
            buffer.flip();
            pendingJpegSurfaces.remove(surface);
            pendingPhotoSurface = null;
            LogUtil.log("ã€CSã€‘å·²æ›¿æ¢ JPEG ImageReader è¾“å‡º: " + surface + " å¤§å°=" + jpegBytes.length);
            return true;
        } catch (Exception e) {
            LogUtil.log("ã€CSã€‘æ›¿æ¢ JPEG Image å¤±è´¥: " + e);
            return false;
        }
    }

    public void createOrPumpImage(Surface targetSurface) {
        if (Build.VERSION.SDK_INT < Build.VERSION_CODES.M)
            return;
        try {
            // ä»…ä½œä¸ºæ—§è·¯å¾„å›žé€€ï¼šæ–°çš„ JPEG æ›¿æ¢é€»è¾‘åœ¨ acquireNextImage/acquireLatestImage ä¸Šå®Œæˆã€‚
            ImageWriter writer = imageWriterMap.get(targetSurface);
            if (writer == null) {
                writer = ImageWriter.newInstance(targetSurface, 2);
                imageWriterMap.put(targetSurface, writer);
            }
            Image image = writer.dequeueInputImage();
            if (image == null)
                return;

            ByteBuffer buffer = image.getPlanes()[0].getBuffer();
            byte[] jpegBytes = createFakeJpegBytes(targetSurface, buffer.capacity());
            if (jpegBytes == null) {
                image.close();
                return;
            }
            buffer.clear();
            buffer.put(jpegBytes);
            buffer.flip();
            writer.queueInputImage(image);
            LogUtil.log("ã€CSã€‘æˆåŠŸæ³µå…¥ä¸€å¼ ä¼ªé€ å›¾ç‰‡ (" + jpegBytes.length + " bytes)");
        } catch (Exception e) {
            LogUtil.log("ã€CSã€‘ç…§ç‰‡æ³¨å…¥å¤±è´¥: " + e);
        }
    }

    // =====================================================================
    // API 101 utilities
    // =====================================================================

    private static Method resolveMethodOnClass(Class<?> clazz, String methodName,
            Class<?>... parameterTypes) throws NoSuchMethodException {
        Class<?> current = clazz;
        while (current != null) {
            try {
                Method m = current.getDeclaredMethod(methodName, parameterTypes);
                m.setAccessible(true);
                return m;
            } catch (NoSuchMethodException ignored) {
                current = current.getSuperclass();
            }
        }
        throw new NoSuchMethodException(clazz.getName() + "#" + methodName);
    }

    private static Object[] toArgs(List<Object> args) {
        return args.toArray(new Object[0]);
    }
}
