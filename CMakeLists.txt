add_clang_executable(boogie-gen BoogieGen.cpp)
target_link_libraries(boogie-gen clangTooling)
