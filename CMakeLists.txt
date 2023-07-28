cmake_minimum_required(VERSION 3.26.4)

project(everload_trie VERSION 0.1)

# if inside subdirectory of another project
if(CMAKE_CURRENT_SOURCE_DIR STREQUAL CMAKE_SOURCE_DIR)
    set(${PROJECT_NAME}_sub OFF)
else()
    set(${PROJECT_NAME}_sub ON)
endif()

add_library(everload_trie INTERFACE include/everload_trie/trie.h)
target_include_directories(everload_trie INTERFACE include)

function(set_target_build_settings target)
    if(NOT TARGET ${target})
        message(FATAL_ERROR "Not target ${target}")
    endif()

    set_target_properties(${target} PROPERTIES CXX_STANDARD 20)

    set(flags --coverage -fsanitize=address -fsanitize=undefined -fsanitize=leak -fsanitize-address-use-after-scope)

    if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
        target_compile_options(${target} PRIVATE "$<$<CONFIG:DEBUG>:${flags}>")
        target_link_options(${target} PRIVATE "$<$<CONFIG:DEBUG>:${flags}>")
    elseif(CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
        arget_compile_options(${target} PRIVATE "$<$<CONFIG:DEBUG>:${flags}>")
        target_link_options(${target} PRIVATE "$<$<CONFIG:DEBUG>:${flags}>")
    else()
        message(FATAL_ERROR "Unknown compiler ${CMAKE_CXX_COMPILER_ID}")
    endif()
endfunction()

if(CMAKE_BUILD_TYPE STREQUAL "Debug")
    add_custom_command(OUTPUT ${CMAKE_BINARY_DIR}/cov.sh
    COMMAND ${CMAKE_COMMAND} -E copy ${PROJECT_SOURCE_DIR}/scripts/cov.sh ${CMAKE_BINARY_DIR}
    DEPENDS scripts/cov.sh)
    add_custom_target(${PROJECT_NAME}_cov ALL DEPENDS ${CMAKE_BINARY_DIR}/cov.sh)
    set_property(DIRECTORY APPEND PROPERTY ADDITIONAL_MAKE_CLEAN_FILES ${CMAKE_BINARY_DIR}/dcov)
endif()

option(${PROJECT_NAME}_TESTING "Enable testing" OFF)
if(${PROJECT_NAME}_TESTING)
    enable_testing()
    if(NOT ${PROJECT_NAME}_sub)
        find_package(Catch2 REQUIRED QUIET)
    endif()
    add_executable(test_${PROJECT_NAME} test/trie.cpp)
    target_link_libraries(test_${PROJECT_NAME} Catch2::Catch2WithMain ${PROJECT_NAME})
    set_target_build_settings(test_${PROJECT_NAME})
    add_test(test_${PROJECT_NAME} test_${PROJECT_NAME})
endif()
