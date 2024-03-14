cmake_minimum_required(VERSION 3.20)

project(glucose)

set(CMAKE_OSX_ARCHITECTURES ${OSX_ARCH})

set(CMAKE_CXX_FLAGS "-std=c++11")
add_compile_definitions()
find_package(ZLIB REQUIRED)

file(GLOB lib_srcs RELATIVE ${CMAKE_CURRENT_SOURCE_DIR} *.cpp repo/mtl/*.cc repo/core/*.cc repo/simp/*.cc repo/utils/*.cc)
list(REMOVE_ITEM lib_srcs "repo/simp/Main.cc")

IF(WIN32) 
        add_compile_definitions(putc_unlocked=putc)
        add_compile_definitions(gettimeofday=mingw_gettimeofday)
ENDIF()

add_compile_options(-Wno-dangling-else)

include_directories(
        ${JNI_INCLUDE}
        ${CMAKE_CURRENT_SOURCE_DIR}/repo
        ${CMAKE_CURRENT_SOURCE_DIR}/../headers
        ${ZLIB_INCLUDE_DIR})

link_libraries(${ZLIB_LIBRARY})

# base library
add_library(glucose SHARED ${lib_srcs})

