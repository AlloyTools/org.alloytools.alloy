cmake_minimum_required(VERSION 3.0.0 FATAL_ERROR)

project(minisat)

set(MINISAT_VERSION "2.1.0")

set(CMAKE_OSX_ARCHITECTURES ${OSX_ARCH})
find_package(ZLIB)
include_directories(
    ${minisat_SOURCE_DIR}/repo 
    ${CMAKE_CURRENT_SOURCE_DIR}/../headers
    ${JNI_INCLUDE} )

add_definitions(-D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS)

set(MINISAT_LIB_SOURCES
    MiniSat.cc
    repo/minisat/utils/Options.cc
    repo/minisat/utils/System.cc
    repo/minisat/core/Solver.cc
    repo/minisat/simp/SimpSolver.cc)

add_library(minisat-lib SHARED ${MINISAT_LIB_SOURCES})

target_link_libraries(minisat-lib ${ZLIB_LIBRARY})


set_target_properties(minisat-lib
  PROPERTIES
    OUTPUT_NAME "minisat")
