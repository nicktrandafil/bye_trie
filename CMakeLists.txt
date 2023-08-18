cmake_minimum_required(VERSION 3.26.4)

project(everload_trie VERSION 0.1)

option(${PROJECT_NAME}_TESTS "Enable tests" OFF)

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

    set(sancov_flags --coverage -fsanitize=address -fsanitize=undefined -fsanitize=leak
        -fsanitize-address-use-after-scope
    )
    set(warning_flags -Wall -Wextra -Wpedantic -Werror -ftemplate-backtrace-limit=0)
    set(error_flags -Werror)

    set(build_options)
    set(link_options)

    if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
        if(CMAKE_BUILD_TYPE MATCHES "Release|RelWithDebInfo|MinSizeRel")
            set(build_options ${build_options} ${error_flags} -Wno-error=maybe-uninitialized)
        elseif(CMAKE_BUILD_TYPE STREQUAL "Debug")
            set(build_options ${build_options} ${sancov_flags})
            set(link_options ${link_options} ${sancov_flags})
        endif()
    elseif(CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
        set(build_options -Wno-unneeded-internal-declaration)
        if(CMAKE_BUILD_TYPE MATCHES "Release|RelWithDebInfo|MinSizeRel")
            set(build_options ${build_options} ${error_flags})
        elseif(CMAKE_BUILD_TYPE STREQUAL "Debug")
            set(build_options ${build_options} ${sancov_flags})
            set(link_options  ${link_options} ${sancov_flags})
        endif()
    else()
        message(FATAL_ERROR "Unknown compiler ${CMAKE_CXX_COMPILER_ID}")
    endif()

    target_compile_options(${target} PRIVATE ${warning_flags} ${build_options})
    target_link_options(${target} PRIVATE ${link_options})
endfunction()

if(${PROJECT_NAME}_TESTS)
    enable_testing()
    if(NOT ${PROJECT_NAME}_sub)
        find_package(Catch2 REQUIRED QUIET)
    endif()
    add_executable(test_${PROJECT_NAME} test/trie.cpp)
    target_link_libraries(test_${PROJECT_NAME} Catch2::Catch2WithMain ${PROJECT_NAME})
    set_target_build_settings(test_${PROJECT_NAME})
    add_test(test_${PROJECT_NAME} test_${PROJECT_NAME})
endif()

if(${PROJECT_NAME}_TESTS AND CMAKE_BUILD_TYPE STREQUAL "Debug")
    set_property(DIRECTORY APPEND PROPERTY ADDITIONAL_CLEAN_FILES ${CMAKE_BINARY_DIR}/dcov)
    add_custom_command(OUTPUT ${CMAKE_BINARY_DIR}/cov.sh
        COMMAND ${CMAKE_COMMAND} -E copy ${PROJECT_SOURCE_DIR}/scripts/cov.sh ${CMAKE_BINARY_DIR}
        DEPENDS scripts/cov.sh
    )
    add_custom_target(coverage DEPENDS ${CMAKE_BINARY_DIR}/cov.sh
        DEPENDS test_${PROJECT_NAME}
    )
    add_custom_command(TARGET coverage POST_BUILD
        COMMAND ./cov.sh
        WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
    )
endif()