cmake_minimum_required(VERSION 3.0.0 FATAL_ERROR)

project(lingeling)

set(VERSION "sc2022")
find_package(Threads REQUIRED)

add_custom_command(
    PRE_BUILD
    COMMAND ./configure
    COMMAND make lglcfg.h lglcflags.h
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}/repo
    OUTPUT lglcfg.h
)

set(CMAKE_BUILD_TYPE Debug)
set(CMAKE_OSX_ARCHITECTURES ${OSX_ARCH})

include_directories(
    ${lingeling_SOURCE_DIR}/repo 
    ${lingeling_SOURCE_DIR}         
    ${CMAKE_CURRENT_SOURCE_DIR}/../headers
    ${JNI_INCLUDE} )

add_definitions(-Wall -O3 -DNLGLOG -DNDEBUG -DNCHKSOL -DNLGLDRUPLIG -DNLGLYALSAT -DNLGLFILES -DNLGLDEMA )

set(LIB_SOURCES
    repo/lglib.c repo/lglbnr.c repo/lgldimacs.c repo/lglopts.c
)

add_executable(plingeling ${LIB_SOURCES} repo/plingeling.c)
target_link_libraries(plingeling PRIVATE ${CMAKE_THREAD_LIBS_INIT}  m)
