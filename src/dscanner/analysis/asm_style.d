//          Copyright Brian Schott (Hackerpilot) 2014.
// Distributed under the Boost Software License, Version 1.0.
//    (See accompanying file LICENSE_1_0.txt or copy at
//          http://www.boost.org/LICENSE_1_0.txt)

module dscanner.analysis.asm_style;

import std.stdio;
import dscanner.analysis.base;
import dscanner.analysis.helpers;
import dmd.tokens;

/**
 * Checks for confusing asm expressions.
 * See_also: $(LINK https://issues.dlang.org/show_bug.cgi?id=9738)
 */
extern (C++) class AsmStyleCheck(AST) : BaseAnalyzerDmd
{
	alias visit = BaseAnalyzerDmd.visit;
	mixin AnalyzerInfo!"asm_style_check";

	extern (D) this(string fileName, bool skipTests = false)
	{
		super(fileName, skipTests);
	}

	override void visit(AST.AsmStatement asmStatement)
	{
		for (Token* token = asmStatement.tokens; token !is null; token = token.next)
		{
			addErrorMessage(brExp, KEY,
					"This is confusing because it looks like an array index. Rewrite a[1] as [a + 1] to clarify.");
		}
	}

	private enum string KEY = "dscanner.confusing.brexp";
}

unittest
{
	import dscanner.analysis.config : StaticAnalysisConfig, Check, disabledConfig;

	StaticAnalysisConfig sac = disabledConfig();
	sac.asm_style_check = Check.enabled;
	assertAnalyzerWarningsDMD(q{
		void testAsm()
		{
			asm
			{
				mov a, someArray[1]; // [warn]: This is confusing because it looks like an array index. Rewrite a[1] as [a + 1] to clarify.
				add near ptr [EAX], 3;
			}
		}
	}c, sac);

	stderr.writeln("Unittest for AsmStyleCheck passed.");
}
