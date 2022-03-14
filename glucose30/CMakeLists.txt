CHECK_IF_DEBUG()
file(GLOB_RECURSE GLUCOSE RELATIVE ${CMAKE_CURRENT_SOURCE_DIR} **)
add_library (glucose30 ${GLUCOSE})

set_target_properties(glucose30 PROPERTIES LINKER_LANGUAGE CXX)
target_include_directories (glucose30 PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
