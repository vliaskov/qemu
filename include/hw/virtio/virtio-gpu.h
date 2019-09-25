/*
 * Virtio GPU Device
 *
 * Copyright Red Hat, Inc. 2013-2014
 *
 * Authors:
 *     Dave Airlie <airlied@redhat.com>
 *     Gerd Hoffmann <kraxel@redhat.com>
 *
 * This work is licensed under the terms of the GNU GPL, version 2.
 * See the COPYING file in the top-level directory.
 */

#ifndef HW_VIRTIO_GPU_H
#define HW_VIRTIO_GPU_H

#include "qemu/queue.h"
#include "ui/qemu-pixman.h"
#include "ui/console.h"
#include "hw/virtio/virtio.h"
#include "qemu/log.h"
#include "sysemu/vhost-user-backend.h"

#include "standard-headers/linux/virtio_gpu.h"

#define TYPE_VIRTIO_GPU_BASE "virtio-gpu-base"
#define VIRTIO_GPU_BASE(obj)                                                \
    OBJECT_CHECK(VirtIOGPUBase, (obj), TYPE_VIRTIO_GPU_BASE)
#define VIRTIO_GPU_BASE_GET_CLASS(obj)                                      \
    OBJECT_GET_CLASS(VirtIOGPUBaseClass, obj, TYPE_VIRTIO_GPU_BASE)
#define VIRTIO_GPU_BASE_CLASS(klass)                                        \
    OBJECT_CLASS_CHECK(VirtIOGPUBaseClass, klass, TYPE_VIRTIO_GPU_BASE)

#define TYPE_VIRTIO_GPU "virtio-gpu-device"
#define VIRTIO_GPU(obj)                                        \
        OBJECT_CHECK(VirtIOGPU, (obj), TYPE_VIRTIO_GPU)

#define TYPE_VHOST_USER_GPU "vhost-user-gpu"

#define VIRTIO_ID_GPU 16

typedef enum virtio_gpu_resource_type {
    VIRTIO_GPU_RES_TYPE_DEFAULT = 0,
    VIRTIO_GPU_RES_TYPE_SHARED
} virtio_gpu_resource_type;

struct virtio_gpu_simple_resource {
    uint32_t resource_id;
    virtio_gpu_resource_type type;
    uint32_t width;
    uint32_t height;
    uint32_t stride;
    uint32_t format;
    uint64_t *addrs;
    struct iovec *iov;
    unsigned int iov_cnt;
    uint32_t scanout_bitmask;
    pixman_image_t *image;
    uint64_t hostmem;

    /* for VIRTIO_GPU_RES_TYPE_SHARED */
    QemuDmaBuf *dmabuf;
    size_t remapsz;
    uint8_t *remapped;

    QTAILQ_ENTRY(virtio_gpu_simple_resource) next;
};

struct virtio_gpu_scanout {
    QemuConsole *con;
    DisplaySurface *ds;
    uint32_t width, height;
    int x, y;
    int invalidate;
    uint32_t resource_id;
    struct virtio_gpu_update_cursor cursor;
    QEMUCursor *current_cursor;
};

struct virtio_gpu_requested_state {
    uint32_t width, height;
    int x, y;
};

enum virtio_gpu_base_conf_flags {
    VIRTIO_GPU_FLAG_VIRGL_ENABLED = 1,
    VIRTIO_GPU_FLAG_STATS_ENABLED,
    VIRTIO_GPU_FLAG_EDID_ENABLED,
    VIRTIO_GPU_FLAG_SHARED_ENABLED,
    VIRTIO_GPU_FLAG_BLOB_ENABLED,
};

#define virtio_gpu_virgl_enabled(_cfg) \
    (_cfg.flags & (1 << VIRTIO_GPU_FLAG_VIRGL_ENABLED))
#define virtio_gpu_stats_enabled(_cfg) \
    (_cfg.flags & (1 << VIRTIO_GPU_FLAG_STATS_ENABLED))
#define virtio_gpu_edid_enabled(_cfg) \
    (_cfg.flags & (1 << VIRTIO_GPU_FLAG_EDID_ENABLED))
#define virtio_gpu_shared_enabled(_cfg) \
    (_cfg.flags & (1 << VIRTIO_GPU_FLAG_SHARED_ENABLED))
#define virtio_gpu_blob_enabled(_cfg) \
    (_cfg.flags & (1 << VIRTIO_GPU_FLAG_BLOB_ENABLED))
#define virtio_gpu_hostmem_enabled(_cfg) \
    (_cfg.hostmem > 0)

struct virtio_gpu_base_conf {
    uint32_t max_outputs;
    uint32_t flags;
    uint32_t xres;
    uint32_t yres;
    uint64_t hostmem;
};

struct virtio_gpu_ctrl_command {
    VirtQueueElement elem;
    VirtQueue *vq;
    struct virtio_gpu_ctrl_hdr cmd_hdr;
    uint32_t error;
    bool finished;
    QTAILQ_ENTRY(virtio_gpu_ctrl_command) next;
};

typedef struct VirtIOGPUBase {
    VirtIODevice parent_obj;

    Error *migration_blocker;

    struct virtio_gpu_base_conf conf;
    struct virtio_gpu_config virtio_config;

    bool use_virgl_renderer;
    int renderer_blocked;
    int enable;

    MemoryRegion hostmem;

    struct virtio_gpu_scanout scanout[VIRTIO_GPU_MAX_SCANOUTS];

    int enabled_output_bitmask;
    struct virtio_gpu_requested_state req_state[VIRTIO_GPU_MAX_SCANOUTS];
} VirtIOGPUBase;

typedef struct VirtIOGPUBaseClass {
    VirtioDeviceClass parent;

    void (*gl_unblock)(VirtIOGPUBase *g);
} VirtIOGPUBaseClass;

#define VIRTIO_GPU_BASE_PROPERTIES(_state, _conf)                       \
    DEFINE_PROP_UINT32("max_outputs", _state, _conf.max_outputs, 1),    \
    DEFINE_PROP_BIT("edid", _state, _conf.flags, \
                    VIRTIO_GPU_FLAG_EDID_ENABLED, true), \
    DEFINE_PROP_UINT32("xres", _state, _conf.xres, 1024), \
    DEFINE_PROP_UINT32("yres", _state, _conf.yres, 768)

typedef struct VirtIOGPU {
    VirtIOGPUBase parent_obj;

    uint64_t conf_max_hostmem;

    VirtQueue *ctrl_vq;
    VirtQueue *cursor_vq;

    QEMUBH *ctrl_bh;
    QEMUBH *cursor_bh;

    QTAILQ_HEAD(, virtio_gpu_simple_resource) reslist;
    QTAILQ_HEAD(, virtio_gpu_ctrl_command) cmdq;
    QTAILQ_HEAD(, virtio_gpu_ctrl_command) fenceq;

    uint64_t hostmem;

    bool renderer_inited;
    bool renderer_reset;
    QEMUTimer *fence_poll;
    QEMUTimer *print_stats;

    uint32_t inflight;
    struct {
        uint32_t max_inflight;
        uint32_t requests;
        uint32_t req_3d;
        uint32_t bytes_3d;
    } stats;
} VirtIOGPU;

typedef struct VhostUserGPU {
    VirtIOGPUBase parent_obj;

    VhostUserBackend *vhost;
    int vhost_gpu_fd; /* closed by the chardev */
    CharBackend vhost_chr;
    QemuDmaBuf dmabuf[VIRTIO_GPU_MAX_SCANOUTS];
    bool backend_blocked;
} VhostUserGPU;

extern const GraphicHwOps virtio_gpu_ops;

#define VIRTIO_GPU_FILL_CMD(out) do {                                   \
        size_t s;                                                       \
        s = iov_to_buf(cmd->elem.out_sg, cmd->elem.out_num, 0,          \
                       &out, sizeof(out));                              \
        if (s != sizeof(out)) {                                         \
            qemu_log_mask(LOG_GUEST_ERROR,                              \
                          "%s: command size incorrect %zu vs %zu\n",    \
                          __func__, s, sizeof(out));                    \
            return;                                                     \
        }                                                               \
    } while (0)

/* virtio-gpu-base.c */
bool virtio_gpu_base_device_realize(DeviceState *qdev,
                                    VirtIOHandleOutput ctrl_cb,
                                    VirtIOHandleOutput cursor_cb,
                                    Error **errp);
void virtio_gpu_base_reset(VirtIOGPUBase *g);
void virtio_gpu_base_fill_display_info(VirtIOGPUBase *g,
                        struct virtio_gpu_resp_display_info *dpy_info);

/* virtio-gpu.c */
void virtio_gpu_ctrl_response(VirtIOGPU *g,
                              struct virtio_gpu_ctrl_command *cmd,
                              struct virtio_gpu_ctrl_hdr *resp,
                              size_t resp_len);
void virtio_gpu_ctrl_response_nodata(VirtIOGPU *g,
                                     struct virtio_gpu_ctrl_command *cmd,
                                     enum virtio_gpu_ctrl_type type);
void virtio_gpu_get_display_info(VirtIOGPU *g,
                                 struct virtio_gpu_ctrl_command *cmd);
void virtio_gpu_get_edid(VirtIOGPU *g,
                         struct virtio_gpu_ctrl_command *cmd);
int virtio_gpu_create_mapping_iov(VirtIOGPU *g,
                                  struct virtio_gpu_resource_attach_backing *ab,
                                  struct virtio_gpu_ctrl_command *cmd,
                                  uint64_t **addr, struct iovec **iov);
void virtio_gpu_cleanup_mapping_iov(VirtIOGPU *g,
                                    struct iovec *iov, uint32_t count);
void virtio_gpu_process_cmdq(VirtIOGPU *g);

/* virtio-gpu-udmabuf.c */
bool virtio_gpu_have_udmabuf(void);
void virtio_gpu_init_udmabuf(struct virtio_gpu_simple_resource *res);
void virtio_gpu_fini_udmabuf(struct virtio_gpu_simple_resource *res);

/* virtio-gpu-3d.c */
void virtio_gpu_virgl_process_cmd(VirtIOGPU *g,
                                  struct virtio_gpu_ctrl_command *cmd);
void virtio_gpu_virgl_fence_poll(VirtIOGPU *g);
void virtio_gpu_virgl_reset(VirtIOGPU *g);
int virtio_gpu_virgl_init(VirtIOGPU *g);
int virtio_gpu_virgl_get_num_capsets(VirtIOGPU *g);

#endif
