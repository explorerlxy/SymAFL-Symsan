#pragma once

#include "worker_ipc.hpp"
#include "pcbt.hpp"

namespace symafl {

void pack_node(const pcbt::Tree &tree, pcbt::NodeRef ref, ShmNode *out);

// Copy newly appended preds/nodes then release-store changed parent links.
void publish_tree(SedbtShm *shm, const pcbt::Tree &tree);

WalkResult check_input(const SedbtShm *shm, const uint8_t *input, uint32_t len);

void *create_shm(const char *name, size_t bytes, int *fd_out);
void *open_shm(const char *name, size_t bytes, int *fd_out);

}  // namespace symafl
