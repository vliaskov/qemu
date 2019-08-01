/*
 * Virtio GPU Device
 *
 * Copyright Red Hat, Inc. 2013-2014
 *
 * Authors:
 *     Dave Airlie <airlied@redhat.com>
 *     Gerd Hoffmann <kraxel@redhat.com>
 *
 * This header is BSD licensed so anyone can use the definitions
 * to implement compatible drivers/servers:
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of IBM nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL IBM OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF
 * USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT
 * OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#ifndef VIRTIO_GPU_HW_H
#define VIRTIO_GPU_HW_H

#include "standard-headers/linux/types.h"

#define VIRTIO_GPU_F_VIRGL 0
#define VIRTIO_GPU_F_EDID  1
/*
 * VIRTIO_GPU_CMD_MEMORY_CREATE
 * VIRTIO_GPU_CMD_MEMORY_UNREF
 * VIRTIO_GPU_CMD_RESOURCE_CREATE_V2
 * VIRTIO_GPU_CMD_RESOURCE_ATTACH_MEMORY
 */
#define VIRTIO_GPU_F_MEMORY              2

/*
 * supports memory type:
 *   VIRTIO_GPU_MEMORY_SHARED_GUEST
 */
#define VIRTIO_GPU_F_MEM_SHARED_GUEST    3

/*
 * supports memory type:
 *   VIRTIO_GPU_MEMORY_HOST_COHERENT
 */
#define VIRTIO_GPU_F_MEM_HOST_COHERENT   4

/*
 * supports memory type:
 *   VIRTIO_GPU_MEMORY_HOST_SYNC
 */
#define VIRTIO_GPU_F_MEM_HOST_SYNC       5

/*
 * supports memory type:
 *   VIRTIO_GPU_MEMORY_HOST_LOCAL
 */
#define VIRTIO_GPU_F_MEM_HOST_LOCAL      6

enum virtio_gpu_ctrl_type {
	VIRTIO_GPU_UNDEFINED = 0,

	/* 2d commands */
	VIRTIO_GPU_CMD_GET_DISPLAY_INFO = 0x0100,
	VIRTIO_GPU_CMD_RESOURCE_CREATE_2D,
	VIRTIO_GPU_CMD_RESOURCE_UNREF,
	VIRTIO_GPU_CMD_SET_SCANOUT,
	VIRTIO_GPU_CMD_RESOURCE_FLUSH,
	VIRTIO_GPU_CMD_TRANSFER_TO_HOST_2D,
	VIRTIO_GPU_CMD_RESOURCE_ATTACH_BACKING,
	VIRTIO_GPU_CMD_RESOURCE_DETACH_BACKING,
	VIRTIO_GPU_CMD_GET_CAPSET_INFO,
	VIRTIO_GPU_CMD_GET_CAPSET,
	VIRTIO_GPU_CMD_GET_EDID,
	VIRTIO_GPU_CMD_MEMORY_CREATE, //267 2 
	VIRTIO_GPU_CMD_MEMORY_UNREF,
	VIRTIO_GPU_CMD_RESOURCE_ATTACH_MEMORY, //269 3
	VIRTIO_GPU_CMD_RESOURCE_CREATE_V2, //270 1
	VIRTIO_GPU_CMD_MEMORY_MAP,

	/* 3d commands */
	VIRTIO_GPU_CMD_CTX_CREATE = 0x0200,
	VIRTIO_GPU_CMD_CTX_DESTROY,
	VIRTIO_GPU_CMD_CTX_ATTACH_RESOURCE,
	VIRTIO_GPU_CMD_CTX_DETACH_RESOURCE,
	VIRTIO_GPU_CMD_RESOURCE_CREATE_3D,
	VIRTIO_GPU_CMD_TRANSFER_TO_HOST_3D,
	VIRTIO_GPU_CMD_TRANSFER_FROM_HOST_3D,
	VIRTIO_GPU_CMD_SUBMIT_3D,

	/* cursor commands */
	VIRTIO_GPU_CMD_UPDATE_CURSOR = 0x0300,
	VIRTIO_GPU_CMD_MOVE_CURSOR,

	/* success responses */
	VIRTIO_GPU_RESP_OK_NODATA = 0x1100,
	VIRTIO_GPU_RESP_OK_DISPLAY_INFO,
	VIRTIO_GPU_RESP_OK_CAPSET_INFO,
	VIRTIO_GPU_RESP_OK_CAPSET,
	VIRTIO_GPU_RESP_OK_EDID,
	VIRTIO_GPU_RESP_OK_RESOURCE_INFO,

	/* error responses */
	VIRTIO_GPU_RESP_ERR_UNSPEC = 0x1200,
	VIRTIO_GPU_RESP_ERR_OUT_OF_MEMORY,
	VIRTIO_GPU_RESP_ERR_INVALID_SCANOUT_ID,
	VIRTIO_GPU_RESP_ERR_INVALID_RESOURCE_ID,
	VIRTIO_GPU_RESP_ERR_INVALID_CONTEXT_ID,
	VIRTIO_GPU_RESP_ERR_INVALID_PARAMETER,
	VIRTIO_GPU_RESP_ERR_INVALID_MEMORY_ID,
};

enum virtio_gpu_memory_type {
	VIRTIO_GPU_MEMORY_UNDEFINED = 0,

	/*
	 * Traditional virtio-gpu memory.
	 * Has both host and guest side storage.
	 *
	 * VIRTIO_GPU_CMD_TRANSFER_* commands are used
	 * to copy between guest and host storage.
	 *
	 * Created using VIRTIO_GPU_CMD_MEMORY_CREATE.
	 */
	VIRTIO_GPU_MEMORY_TRANSFER,

	/*
	 * Shared storage. allocated by guest.
	 *
	 * Created using VIRTIO_GPU_CMD_MEMORY_CREATE.
	 */
	VIRTIO_GPU_MEMORY_SHARED_GUEST,

	/*
	 * Host allocated storage.
	 *
	 * Created using VIRTIO_GPU_CMD_MEMORY_HOST_CREATE.
	 *
	 * In practice that will be host gpu buffer objects
	 * allocated using gbm.
	 *
	 * VIRTIO_GPU_MEMORY_HOST_COHERENT
	 *   Can be mapped into the guest, using virtio
	 *   shared memory (VIRTIO_PCI_CAP_SHARED_MEMORY_CFG).
	 *
	 * VIRTIO_GPU_MEMORY_HOST_SYNC
	 *   Can be mapped into the guest, using virtio
	 *   shared memory (VIRTIO_PCI_CAP_SHARED_MEMORY_CFG).
	 *   Not coherent, requires explicit flushing.
	 *
	 * VIRTIO_GPU_MEMORY_HOST_LOCAL
	 *   Can not be mapped into the guest.  Expected to be used
	 *   for memory the host can't map either (unmappable device
	 *   memory).
	 */
	VIRTIO_GPU_MEMORY_HOST_COHERENT,
	VIRTIO_GPU_MEMORY_HOST_SYNC,
	VIRTIO_GPU_MEMORY_HOST_LOCAL,
};

#define VIRTIO_GPU_FLAG_FENCE (1 << 0)

struct virtio_gpu_ctrl_hdr {
	uint32_t type;
	uint32_t flags;
	uint64_t fence_id;
	uint32_t ctx_id;
	uint32_t padding;
};

/* data passed in the cursor vq */

struct virtio_gpu_cursor_pos {
	uint32_t scanout_id;
	uint32_t x;
	uint32_t y;
	uint32_t padding;
};

/* VIRTIO_GPU_CMD_UPDATE_CURSOR, VIRTIO_GPU_CMD_MOVE_CURSOR */
struct virtio_gpu_update_cursor {
	struct virtio_gpu_ctrl_hdr hdr;
	struct virtio_gpu_cursor_pos pos;  /* update & move */
	uint32_t resource_id;           /* update only */
	uint32_t hot_x;                 /* update only */
	uint32_t hot_y;                 /* update only */
	uint32_t padding;
};

/* data passed in the control vq, 2d related */

struct virtio_gpu_rect {
	uint32_t x;
	uint32_t y;
	uint32_t width;
	uint32_t height;
};

/* VIRTIO_GPU_CMD_RESOURCE_UNREF */
struct virtio_gpu_resource_unref {
	struct virtio_gpu_ctrl_hdr hdr;
	uint32_t resource_id;
	uint32_t padding;
};

/* VIRTIO_GPU_CMD_RESOURCE_CREATE_2D: create a 2d resource with a format */
struct virtio_gpu_resource_create_2d {
	struct virtio_gpu_ctrl_hdr hdr;
	uint32_t resource_id;
	uint32_t format;
	uint32_t width;
	uint32_t height;
};

/* VIRTIO_GPU_CMD_SET_SCANOUT */
struct virtio_gpu_set_scanout {
	struct virtio_gpu_ctrl_hdr hdr;
	struct virtio_gpu_rect r;
	uint32_t scanout_id;
	uint32_t resource_id;
};

/* VIRTIO_GPU_CMD_RESOURCE_FLUSH */
struct virtio_gpu_resource_flush {
	struct virtio_gpu_ctrl_hdr hdr;
	struct virtio_gpu_rect r;
	uint32_t resource_id;
	uint32_t padding;
};

/* VIRTIO_GPU_CMD_TRANSFER_TO_HOST_2D: simple transfer to_host */
struct virtio_gpu_transfer_to_host_2d {
	struct virtio_gpu_ctrl_hdr hdr;
	struct virtio_gpu_rect r;
	uint64_t offset;
	uint32_t resource_id;
	uint32_t padding;
};

struct virtio_gpu_mem_entry {
	uint64_t addr;
	uint32_t length;
	uint32_t padding;
};

/* VIRTIO_GPU_CMD_RESOURCE_ATTACH_BACKING */
struct virtio_gpu_resource_attach_backing {
	struct virtio_gpu_ctrl_hdr hdr;
	uint32_t resource_id;
	uint32_t nr_entries;
};

/* VIRTIO_GPU_CMD_RESOURCE_DETACH_BACKING */
struct virtio_gpu_resource_detach_backing {
	struct virtio_gpu_ctrl_hdr hdr;
	uint32_t resource_id;
	uint32_t padding;
};

/* VIRTIO_GPU_RESP_OK_DISPLAY_INFO */
#define VIRTIO_GPU_MAX_SCANOUTS 16
struct virtio_gpu_resp_display_info {
	struct virtio_gpu_ctrl_hdr hdr;
	struct virtio_gpu_display_one {
		struct virtio_gpu_rect r;
		uint32_t enabled;
		uint32_t flags;
	} pmodes[VIRTIO_GPU_MAX_SCANOUTS];
};

/* data passed in the control vq, 3d related */

struct virtio_gpu_box {
	uint32_t x, y, z;
	uint32_t w, h, d;
};

/* VIRTIO_GPU_CMD_TRANSFER_TO_HOST_3D, VIRTIO_GPU_CMD_TRANSFER_FROM_HOST_3D */
struct virtio_gpu_transfer_host_3d {
	struct virtio_gpu_ctrl_hdr hdr;
	struct virtio_gpu_box box;
	uint64_t offset;
	uint32_t resource_id;
	uint32_t level;
	uint32_t stride;
	uint32_t layer_stride;
};

/* VIRTIO_GPU_CMD_RESOURCE_CREATE_3D */
#define VIRTIO_GPU_RESOURCE_FLAG_Y_0_TOP (1 << 0)
struct virtio_gpu_resource_create_3d {
	struct virtio_gpu_ctrl_hdr hdr;
	uint32_t resource_id;
	/* memory_type is VIRTIO_GPU_MEMORY_TRANSFER */
	uint32_t target;
	uint32_t format;
	uint32_t bind;
	uint32_t width;
	uint32_t height;
	uint32_t depth;
	uint32_t array_size;
	uint32_t last_level;
	uint32_t nr_samples;
	uint32_t flags;
	uint32_t padding;
};

/* VIRTIO_GPU_CMD_CTX_CREATE */
struct virtio_gpu_ctx_create {
	struct virtio_gpu_ctrl_hdr hdr;
	uint32_t nlen;
	uint32_t padding;
	char debug_name[64];
};

/* VIRTIO_GPU_CMD_CTX_DESTROY */
struct virtio_gpu_ctx_destroy {
	struct virtio_gpu_ctrl_hdr hdr;
};

/* VIRTIO_GPU_CMD_CTX_ATTACH_RESOURCE, VIRTIO_GPU_CMD_CTX_DETACH_RESOURCE */
struct virtio_gpu_ctx_resource {
	struct virtio_gpu_ctrl_hdr hdr;
	uint32_t resource_id;
	uint32_t padding;
};

/* VIRTIO_GPU_CMD_SUBMIT_3D */
struct virtio_gpu_cmd_submit {
	struct virtio_gpu_ctrl_hdr hdr;
	uint32_t size;
	uint32_t padding;
};

/* VIRTIO_GPU_CMD_MEMORY_CREATE */
struct virtio_gpu_cmd_memory_create {
	struct virtio_gpu_ctrl_hdr hdr;
	uint32_t memory_id;
	uint32_t memory_type;
	uint32_t flags;
	uint32_t nr_entries;
	/* struct virtio_gpu_mem_entry entries follow here */
};

/* VIRTIO_GPU_CMD_MEMORY_HOST_CREATE */
struct virtio_gpu_cmd_memory_host_create {
	struct virtio_gpu_ctrl_hdr hdr;
	uint32_t memory_id;
	uint32_t memory_type;
	uint32_t flags;
	uint32_t padding;
};

/* VIRTIO_GPU_CMD_MEMORY_MAP */
struct virtio_gpu_cmd_memory_map {
	struct virtio_gpu_ctrl_hdr hdr;
	uint32_t memory_id;
	uint32_t padding;
	uint64_t offset;
};

/* VIRTIO_GPU_CMD_MEMORY_UNREF */
struct virtio_gpu_cmd_memory_unref {
	struct virtio_gpu_ctrl_hdr hdr;
	uint32_t memory_id;
	uint32_t padding;
};

/* VIRTIO_GPU_CMD_RESOURCE_ATTACH_MEMORY */
struct virtio_gpu_cmd_resource_attach_memory {
	struct virtio_gpu_ctrl_hdr hdr;
	uint32_t resource_id;
	uint32_t memory_id;
	uint32_t plane;
	uint32_t padding;
	uint64_t offset;
};

/* VIRTIO_GPU_CMD_RESOURCE_CREATE_V2 */
struct virtio_gpu_cmd_resource_create_v2 {
	struct virtio_gpu_ctrl_hdr hdr;
	uint32_t resource_id;
	uint32_t memory_type;
	uint32_t format;
	uint32_t width;
	uint32_t height;
	/* 3d only */
	uint32_t target;
	uint32_t bind;
	uint32_t depth;
	uint32_t array_size;
	uint32_t last_level;
	uint32_t nr_samples;
	uint32_t flags;
};

/* VIRTIO_GPU_RESP_OK_RESOURCE_INFO */
struct virtio_gpu_resp_resource_info {
	struct virtio_gpu_ctrl_hdr hdr;
	uint32_t align[4];
	uint32_t stride[4];
	uint32_t size[4];
};

#define VIRTIO_GPU_CAPSET_VIRGL 1
#define VIRTIO_GPU_CAPSET_VIRGL2 2

/* VIRTIO_GPU_CMD_GET_CAPSET_INFO */
struct virtio_gpu_get_capset_info {
	struct virtio_gpu_ctrl_hdr hdr;
	uint32_t capset_index;
	uint32_t padding;
};

/* VIRTIO_GPU_RESP_OK_CAPSET_INFO */
struct virtio_gpu_resp_capset_info {
	struct virtio_gpu_ctrl_hdr hdr;
	uint32_t capset_id;
	uint32_t capset_max_version;
	uint32_t capset_max_size;
	uint32_t padding;
};

/* VIRTIO_GPU_CMD_GET_CAPSET */
struct virtio_gpu_get_capset {
	struct virtio_gpu_ctrl_hdr hdr;
	uint32_t capset_id;
	uint32_t capset_version;
};

/* VIRTIO_GPU_RESP_OK_CAPSET */
struct virtio_gpu_resp_capset {
	struct virtio_gpu_ctrl_hdr hdr;
	uint8_t capset_data[];
};

/* VIRTIO_GPU_CMD_GET_EDID */
struct virtio_gpu_cmd_get_edid {
	struct virtio_gpu_ctrl_hdr hdr;
	uint32_t scanout;
	uint32_t padding;
};

/* VIRTIO_GPU_RESP_OK_EDID */
struct virtio_gpu_resp_edid {
	struct virtio_gpu_ctrl_hdr hdr;
	uint32_t size;
	uint32_t padding;
	uint8_t edid[1024];
};

#define VIRTIO_GPU_EVENT_DISPLAY (1 << 0)

struct virtio_gpu_config {
	uint32_t events_read;
	uint32_t events_clear;
	uint32_t num_scanouts;
	uint32_t num_capsets;
};

/* simple formats for fbcon/X use */
enum virtio_gpu_formats {
	VIRTIO_GPU_FORMAT_B8G8R8A8_UNORM  = 1,
	VIRTIO_GPU_FORMAT_B8G8R8X8_UNORM  = 2,
	VIRTIO_GPU_FORMAT_A8R8G8B8_UNORM  = 3,
	VIRTIO_GPU_FORMAT_X8R8G8B8_UNORM  = 4,

	VIRTIO_GPU_FORMAT_R8G8B8A8_UNORM  = 67,
	VIRTIO_GPU_FORMAT_X8B8G8R8_UNORM  = 68,

	VIRTIO_GPU_FORMAT_A8B8G8R8_UNORM  = 121,
	VIRTIO_GPU_FORMAT_R8G8B8X8_UNORM  = 134,
};

#endif
