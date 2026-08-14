## custom_mutation for AFL++

project(SymSanMutator C CXX)

set(CMAKE_POSITION_INDEPENDENT_CODE ON)
set(CMAKE_CXX_STANDARD 17)

# set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -stdlib=libc++")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O3 -g -mcx16 -march=native -fno-builtin-malloc -fno-builtin-calloc -fno-builtin-realloc -fno-builtin-free")
if (ASAN_BUILD)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fsanitize=address")
endif()

if (NOT IS_DIRECTORY "${AFLPP_PATH}/include")
  message(FATAL_ERROR "Invalid AFL++ directory path! ${AFLPP_PATH}")
endif()

add_library(SymSanMutator SHARED
  symsan.cpp pcbt.cpp pred.cpp shm_sedbt.cpp worker_client.cpp)
target_include_directories(SymSanMutator PRIVATE
  ${CMAKE_CURRENT_SOURCE_DIR}/../../runtime
  ${AFLPP_PATH}/include
)
target_link_libraries(SymSanMutator
  launcher
  rt
)

add_executable(symafl-worker
  symafl_worker.cpp shm_sedbt.cpp pcbt.cpp pred.cpp)
target_include_directories(symafl-worker PRIVATE
  ${CMAKE_CURRENT_SOURCE_DIR}/../../runtime
  ${AFLPP_PATH}/include
)
target_compile_features(symafl-worker PRIVATE cxx_std_17)
target_link_libraries(symafl-worker rt)
add_custom_command(TARGET symafl-worker POST_BUILD
  COMMAND ${CMAKE_COMMAND} -E make_directory
          "${CMAKE_INSTALL_PREFIX}/${SYMSAN_BIN_DIR}"
  COMMAND ${CMAKE_COMMAND} -E copy $<TARGET_FILE:symafl-worker>
          "${CMAKE_INSTALL_PREFIX}/${SYMSAN_BIN_DIR}/")
add_custom_command(TARGET SymSanMutator POST_BUILD
  COMMAND ${CMAKE_COMMAND} -E make_directory
          "${CMAKE_INSTALL_PREFIX}/${SYMSAN_BIN_DIR}"
  COMMAND ${CMAKE_COMMAND} -E copy $<TARGET_FILE:SymSanMutator>
          "${CMAKE_INSTALL_PREFIX}/${SYMSAN_BIN_DIR}/")
if (ASAN_BUILD)
  target_link_libraries(SymSanMutator
    ${LLVM_BINARY_DIR}/lib/clang/12.0.1/lib/linux/libclang_rt.asan-x86_64.a
  )
endif()

install (TARGETS symafl-worker DESTINATION ${SYMSAN_BIN_DIR})
install (TARGETS SymSanMutator DESTINATION ${SYMSAN_BIN_DIR})
