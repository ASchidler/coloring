CHECK_IF_DEBUG()
file(GLOB_RECURSE CADICAL RELATIVE ${CMAKE_CURRENT_SOURCE_DIR} *)
add_library (cadical ${CADICAL})

set_target_properties(cadical PROPERTIES LINKER_LANGUAGE CXX)
target_include_directories (cadical PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
