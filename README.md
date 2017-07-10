# boogie-gen

## To setup and build

1. Clone the LLVM repo from https://github.com/llvm-mirror/llvm 
2. Clone the CLANG repo from https://github.com/llvm-mirror/clang inside the LLVM repo's tools folder
3. Clone this repo inside the CLANG repo's tools folder.
4. Edit the `CMakeLists.txt` inside the clang/tools folder and add the line
   
   `add_clang_subdirectory(boogie-gen)`
   
5. Build LLVM and CLANG using instructions at http://llvm.org/docs/CMake.html

You will now find boogie-gen.exe in your build/[Debug|Release]/bin folder. (Depending on the configuration you built in).

## To Use
1. Add boogie-gen.exe to the %PATH% so it can be invoked directly from any working directory.
2. To generate boogie code for any C file use
    
   `boogie-gen.exe filename.c --`
   
3. This will generate `test.bpl` in the working directory.


