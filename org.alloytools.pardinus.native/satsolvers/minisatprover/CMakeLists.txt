cmake_minimum_required(VERSION 3.20 FATAL_ERROR)

project(minisatprover)

set(MINISATP_VERSION "1.1.0")


include_directories(
    ${minisatprover_SOURCE_DIR}/repo 
    ${JNI_INCLUDE} 
    ${minisatprover_SOURCE_DIR}/repo/ADTs         
    ${CMAKE_CURRENT_SOURCE_DIR}/../headers
)
set(CMAKE_OSX_ARCHITECTURES ${OSX_ARCH})

set(MINISATP_LIB_SOURCES
    MiniSatProver.cpp
    repo/File.C
    repo/Proof.C
    repo/Solver.C
)

add_library(libminisatprover SHARED ${MINISATP_LIB_SOURCES})
add_definitions(-Wno-deprecated-declarations -Wno-deprecated)
target_link_libraries(libminisatprover ${GMP_LIBRARY})

set_target_properties(libminisatprover
  PROPERTIES
    OUTPUT_NAME "minisatprover" 
    VERSION ${MINISATP_VERSION})
