/*
 * Copyright (c) 2016, Oracle and/or its affiliates.
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without modification, are
 * permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice, this list of
 * conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice, this list of
 * conditions and the following disclaimer in the documentation and/or other materials provided
 * with the distribution.
 *
 * 3. Neither the name of the copyright holder nor the names of its contributors may be used to
 * endorse or promote products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS
 * OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE
 * GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED
 * AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 */
package com.oracle.truffle.llvm.tools;

import java.io.File;

import com.oracle.truffle.llvm.tools.LLVMToolPaths.LLVMTool;
import com.oracle.truffle.llvm.tools.util.ProcessUtil;

public final class LLVMAssembler {

    private LLVMAssembler() {
    }

    public static void assembleToBitcodeFile(File irFile) {
        String compilationCommand = LLVMToolPaths.getLLVMProgram(LLVMTool.ASSEMBLER) + " " + irFile.getAbsolutePath();
        ProcessUtil.executeNativeCommandZeroReturn(compilationCommand);
    }

    public static void assembleToBitcodeFile(File irFile, File destFile) {
        if (!irFile.getAbsolutePath().endsWith(".ll")) {
            throw new IllegalArgumentException("Can only assemble .ll files!");
        }
        final String args = " -o=" + destFile.getAbsolutePath() + " " + irFile.getAbsolutePath();
        final String compilationCommand = LLVMToolPaths.getLLVMProgram(LLVMTool.ASSEMBLER) + args;
        ProcessUtil.executeNativeCommandZeroReturn(compilationCommand);
    }

}
