//          Copyright Brian Schott (Hackerpilot) 2014.
// Distributed under the Boost Software License, Version 1.0.
//    (See accompanying file LICENSE_1_0.txt or copy at
//          http://www.boost.org/LICENSE_1_0.txt)

module dscanner.analysis.enumarrayliteral;

import dscanner.analysis.base;

extern (C++) class EnumArrayVisitor(AST) : BaseAnalyzerDmd
{
	alias visit = BaseAnalyzerDmd.visit;
	mixin AnalyzerInfo!"enum_array_literal_check";

	private enum KEY = "dscanner.performance.enum_array_literal";

	extern (D) this(string fileName)
	{
		super(fileName);
	}

	override void visit(AST.VarDeclaration vd)
    {
		import dmd.astenums : STC, InitKind;
		import std.string : toStringz;

		string message = "This enum may lead to unnecessary allocation at run-time. Use 'static immutable "
							~ vd.ident.toString().idup() ~ " = [ ...' instead.";

		if (!vd.type && vd._init.kind == InitKind.array && vd.storage_class & STC.manifest)
		{
			foreach (part; autoDec.parts)
			{
				if (part.initializer is null)
					continue;
				if (part.initializer.nonVoidInitializer is null)
					continue;
				if (part.initializer.nonVoidInitializer.arrayInitializer is null)
					continue;
				addErrorMessage(part.initializer.nonVoidInitializer,
						KEY,
						"This enum may lead to unnecessary allocation at run-time."
						~ " Use 'static immutable "
						~ part.identifier.text ~ " = [ ...' instead.",
						[
							AutoFix.replacement(enumToken[0].token, "static immutable")
						]);
			}
		}

		super.visit(vd);
	}

	private enum string KEY = "dscanner.performance.enum_array_literal";
}

unittest
{
	import dscanner.analysis.config : Check, disabledConfig, StaticAnalysisConfig;
	import dscanner.analysis.helpers : assertAnalyzerWarningsDMD, assertAutoFix;
	import std.stdio : stderr;

	StaticAnalysisConfig sac = disabledConfig();
	sac.enum_array_literal_check = Check.enabled;

	assertAnalyzerWarningsDMD(q{
		enum x = [1, 2, 3]; // [warn]: This enum may lead to unnecessary allocation at run-time. Use 'static immutable x = [ ...' instead.
	}c, sac);

	assertAutoFix(q{
		enum x = [1, 2, 3]; // fix
	}c, q{
		static immutable x = [1, 2, 3]; // fix
	}c, sac);

	stderr.writeln("Unittest for EnumArrayLiteralCheck passed.");
}
