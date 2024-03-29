cmake_minimum_required(VERSION 3.16.3)

project(regularc)

add_custom_command(
    OUTPUT ${CMAKE_SOURCE_DIR}/perltoc.c
    COMMAND xsubpp ${CMAKE_SOURCE_DIR}/perltoc.xs > ${CMAKE_SOURCE_DIR}/perltoc.c
)

find_package(PerlLibs 5.28.0)

find_package(range-v3 REQUIRED)

find_package(zstd REQUIRED)

if(NOT DEFINED ENV{LLVM_CONFIG})
    find_program(LLVM_CONFIG "llvm-config")
else()
    find_program(LLVM_CONFIG $ENV{LLVM_CONFIG})
endif()

execute_process(COMMAND ${LLVM_CONFIG} --libs all
                OUTPUT_VARIABLE llvm_libraries)

execute_process(COMMAND ${LLVM_CONFIG} --includedir
                OUTPUT_VARIABLE llvm_includes)

execute_process(COMMAND ${LLVM_CONFIG} --libdir
                OUTPUT_VARIABLE llvm_libdir)

add_executable(regularc llvmgen.cpp main.c perltoc.c)

if(NOT PERLLIBS_FOUND)
    message(WARNING "Missing perl libraries")
endif()

if(llvm_libraries STREQUAL "")
    message(WARNING "Missing valid LLVM_CONFIG")
endif()

string(STRIP ${llvm_libraries} llvm_libraries)

string(STRIP ${llvm_includes} llvm_includes)

string(STRIP ${llvm_libdir} llvm_libdir)

target_link_directories(regularc PRIVATE ${llvm_libdir})

target_link_libraries(regularc PRIVATE ${llvm_libraries} -rdynamic ${PERL_LIBRARY} -lpthread -lz -lcurses -ldl -lc zstd::libzstd_static range-v3::range-v3)

target_compile_options(regularc PRIVATE -rdynamic -O0 -g3 -fpermissive)

set(CMAKE_C_FLAGS -Wno-error=implicit-function-declaration)

target_include_directories(regularc PRIVATE ${PERL_INCLUDE_PATH} ${llvm_includes} src /opt/local/include)

set_property(TARGET regularc PROPERTY CXX_STANDARD 23)

set_property(TARGET regularc PROPERTY C_STANDARD 90)

set(CMAKE_CXX_VISIBILITY_PRESET default)
