cmake_minimum_required(VERSION 3.10)
project(planarity)

macro (CHECK_IF_DEBUG)
    if (CMAKE_BUILD_TYPE MATCHES Debug)
        set (CMAKE_BUILD_TYPE Release)
    endif()
endmacro()

link_libraries(stdc++fs)
set(CMAKE_CXX_STANDARD 17)
set(Boost_USE_MULTITHREADED ON)
set(Boost_USE_STATIC_LIBS   ON)
find_package(Boost REQUIRED COMPONENTS thread chrono)

add_subdirectory("glucose30")
add_subdirectory("cadical")
SET(CMAKE_CXX_FLAGS  "${CMAKE_CXX_FLAGS} -pthread -lstdc++fs -lpthread -lboost_thread -lboost_chrono -lbz2")

add_executable(planarity-cpp main_benchmark.cpp conflict_graph.h heuristics.h boi.h solution.h geometric.h bucket_queue.h clique.h sat_encode.h sat_search.h planarity.h conflict_graph.cpp sat_encode2.h graph_generator.h reducer.h)

target_link_libraries (planarity-cpp LINK_PUBLIC glucose30 cadical Boost::thread bz2)
#target_link_libraries(planarity-cpp Boost::thread)