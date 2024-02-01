cmake_minimum_required(VERSION 3.22.1)

project(bye_trie VERSION 0.1)

option(${PROJECT_NAME}_TESTS "Enable tests" ON)
option(${PROJECT_NAME}_BENCHMARKS "Enable benchmarks" ON)
option(${PROJECT_NAME}_BOOST_IP "Enable boost::asio::ip::network" ON)
option(${PROJECT_NAME}_DOC "Enable documentation" ON)

# if inside subdirectory of another project
if(CMAKE_CURRENT_SOURCE_DIR STREQUAL CMAKE_SOURCE_DIR)
    set(${PROJECT_NAME}_sub OFF)
else()
    set(${PROJECT_NAME}_sub ON)
endif()

set(sources
    include/bye_trie/bye_trie.h
    include/bye_trie/uint128.h
)

if(${PROJECT_NAME}_BOOST_IP)
    set(sources ${sources} include/bye_trie/ip_net_bye_trie.h)
endif()
add_library(${PROJECT_NAME} INTERFACE ${sources})
target_include_directories(${PROJECT_NAME} INTERFACE include)

if(NOT ${PROJECT_NAME}_sub AND ${PROJECT_NAME}_BOOST_IP)
    find_package(Boost REQUIRED  QUIET)
endif()

if(${PROJECT_NAME}_BOOST_IP)
    target_link_libraries(${PROJECT_NAME} INTERFACE Boost::headers)
endif()


function(set_target_build_settings target)
    if(NOT TARGET ${target})
        message(FATAL_ERROR "Not target ${target}")
    endif()

    set_target_properties(${target} PROPERTIES CXX_STANDARD 20 CXX_STANDARD_REQUIRED ON CXX_EXTENSIONS OFF)

    set(sancov_flags --coverage -fsanitize=address -fsanitize=undefined -fsanitize=leak
        -fsanitize-address-use-after-scope
    )
    set(warning_flags -Wall -Wextra -Wpedantic -Werror -ftemplate-backtrace-limit=0)
    set(error_flags -Werror)

    set(build_options)
    set(link_options)

    if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
        if(CMAKE_BUILD_TYPE MATCHES "Release|RelWithDebInfo|MinSizeRel")
            set(build_options ${build_options} ${error_flags})
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
    set(sources
        test/bye_trie.cpp
        test/pair.h
        test/stress_test.cpp
    )
    if(${PROJECT_NAME}_BOOST_IP)
        set(sources ${sources} test/ip_net_bye_trie.cpp)
    endif()
    add_executable(test_${PROJECT_NAME} ${sources})
    target_link_libraries(test_${PROJECT_NAME} Catch2::Catch2WithMain ${PROJECT_NAME})
    set_target_build_settings(test_${PROJECT_NAME} 20)
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
elseif(${PROJECT_NAME}_TESTS)
    message(NOTICE "Build in Debug mode to enable coverage")
endif()

if(${PROJECT_NAME}_BENCHMARKS)
    if(NOT ${PROJECT_NAME}_BOOST_IP)
        message(FATAL_ERROR "Benchmarks require boost::asio::ip::network")
    endif()
    add_custom_command(OUTPUT ${CMAKE_BINARY_DIR}/uniq_pfx_asn_dfz.csv
        COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_SOURCE_DIR}/bench/uniq_pfx_asn_dfz.csv ${CMAKE_BINARY_DIR}
        DEPENDS bench/uniq_pfx_asn_dfz.csv
    )
    add_custom_target(data DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/uniq_pfx_asn_dfz.csv)
    add_executable(bench_ipv4_networks bench/ipv4_networks.cpp)
    target_link_libraries(bench_ipv4_networks PRIVATE ${PROJECT_NAME})
    set_target_build_settings(bench_ipv4_networks)
    add_dependencies(bench_ipv4_networks data)

    add_executable(bench_throughput bench/throughput.cpp)
    target_link_libraries(bench_throughput PRIVATE ${PROJECT_NAME})
    set_target_build_settings(bench_throughput)

    add_executable(bench_throughput_iar16 bench/throughput_iar16.cpp)
    target_link_libraries(bench_throughput_iar16 PRIVATE ${PROJECT_NAME})
    set_target_build_settings(bench_throughput_iar16)
endif()

if(${PROJECT_NAME}_DOC)
    add_subdirectory(doc)
endif()
