	.text
	.file	"final_llc_test.ll"
	.globl	test                            # -- Begin function test
	.p2align	4, 0x90
	.type	test,@function
test:                                   # @test
	.cfi_startproc
# %bb.0:
                                        # kill: def $edi killed $edi def $rdi
	leal	(%rdi,%rdi), %eax
	retq
.Lfunc_end0:
	.size	test, .Lfunc_end0-test
	.cfi_endproc
                                        # -- End function
	.section	".note.GNU-stack","",@progbits
