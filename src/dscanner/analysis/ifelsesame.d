//          Copyright Brian Schott (Hackerpilot) 2014.
// Distributed under the Boost Software License, Version 1.0.
//    (See accompanying file LICENSE_1_0.txt or copy at
//          http://www.boost.org/LICENSE_1_0.txt)

module dscanner.analysis.ifelsesame;

import dscanner.analysis.base;
import dmd.hdrgen : toChars;
import dmd.tokens : EXP;
import std.conv : to;
import std.string : format;
import std.typecons : Tuple, tuple;

/**
 * Checks for duplicated code in conditional and logical expressions.
 * $(UL
 * $(LI If statements whose "then" block is the same as the "else" block)
 * $(LI || and && expressions where the left and right are the same)
 * $(LI == and != expressions where the left and right are the same)
 * $(LI >, <, >=, and <= expressions where the left and right are the same)
 * $(LI Assignments where the left and right are the same)
 * )
 */
extern (C++) class IfElseSameCheck(AST) : BaseAnalyzerDmd
{
	alias visit = BaseAnalyzerDmd.visit;
	mixin AnalyzerInfo!"if_else_same_check";

	private enum IF_KEY = "dscanner.bugs.if_else_same";
	private enum IF_MESSAGE = "'Else' branch is identical to 'Then' branch.";

	private enum LOGICAL_EXP_KEY = "dscanner.bugs.logic_operator_operands";
	private enum LOGICAL_EXP_MESSAGE = "Left side of logical %s is identical to right side.";

	private enum ASSIGN_KEY = "dscanner.bugs.self_assignment";
	private enum ASSIGN_MESSAGE = "Left side of assignment operation is identical to the right side.";

	private bool inAssignment = false;

	extern (D) this(string fileName, bool skipTests = false)
	{
		super(fileName, skipTests);
	}

	override void visit(AST.IfStatement ifStatement)
	{
		super.visit(ifStatement);

		if (ifStatement.ifbody is null || ifStatement.elsebody is null)
			return;

		auto thenBody = to!string(toChars(ifStatement.ifbody));
		auto elseBody = to!string(toChars(ifStatement.elsebody));

		if (thenBody == elseBody)
		{
			const(Token)[] tokens = ifStatement.elseStatement.tokens;
			// extend 1 past, so we include the `else` token
			tokens = (tokens.ptr - 1)[0 .. tokens.length + 1];
			addErrorMessage(tokens,
					IF_ELSE_SAME_KEY, "'Else' branch is identical to 'Then' branch.");
		}
	}

	override void visit(AST.AssignExp assignExp)
	{
		auto e = cast(const AssignExpression) assignExpression.expression;
		if (e !is null && assignExpression.operator == tok!"="
				&& e.ternaryExpression == assignExpression.ternaryExpression)
		{
			addErrorMessage(assignExpression, SELF_ASSIGNMENT_KEY,
					"Left side of assignment operatior is identical to the right side.");
		}
		assignExpression.accept(this);
	}

	override void visit(AST.CondExp condExp)
	{
		if (andAndExpression.left !is null && andAndExpression.right !is null
				&& andAndExpression.left == andAndExpression.right)
		{
			addErrorMessage(andAndExpression.right,
					LOGIC_OPERATOR_OPERANDS_KEY,
					"Left side of logical and is identical to right side.");
		}
		andAndExpression.accept(this);
	}

	override void visit(AST.LogicalExp logicalExpr)
	{
		super.visit(logicalExpr);
		handleBinaryExpression(logicalExpr);
	}

	private void handleBinaryExpression(AST.BinExp expr)
	{
		auto expr1 = to!string(toChars(expr.e1));
		auto expr2 = to!string(toChars(expr.e2));

		if (expr1 == expr2)
		{
			addErrorMessage(orOrExpression.right,
					LOGIC_OPERATOR_OPERANDS_KEY,
					"Left side of logical or is identical to right side.");
		}
	}

	private extern (D) Tuple!(string, string) getErrorInfo(EXP op)
	{
		switch (op)
		{
		case EXP.orOr:
			return tuple(LOGICAL_EXP_KEY, LOGICAL_EXP_MESSAGE.format("or"));
		case EXP.andAnd:
			return tuple(LOGICAL_EXP_KEY, LOGICAL_EXP_MESSAGE.format("and"));
		case EXP.question:
			return tuple(ASSIGN_KEY, ASSIGN_MESSAGE);
		default:
			assert(0);
		}

	}

private:

	enum string IF_ELSE_SAME_KEY = "dscanner.bugs.if_else_same";
	enum string SELF_ASSIGNMENT_KEY = "dscanner.bugs.self_assignment";
	enum string LOGIC_OPERATOR_OPERANDS_KEY = "dscanner.bugs.logic_operator_operands";
}

unittest
{
	import dscanner.analysis.config : StaticAnalysisConfig, Check, disabledConfig;
	import dscanner.analysis.helpers : assertAnalyzerWarningsDMD;
	import std.stdio : stderr;

	StaticAnalysisConfig sac = disabledConfig();
	sac.if_else_same_check = Check.enabled;

	assertAnalyzerWarningsDMD(q{
		void testThenElseSame()
		{
			string person = "unknown";
			if (person == "unknown") // [warn]: 'Else' branch is identical to 'Then' branch.
				person = "bobrick";
			else
				person = "bobrick";

			if (person == "unknown")
				person = "ricky";
			else
				person = "bobby";
		}
	}c, sac);

	assertAnalyzerWarningsDMD(q{
		void testLogicalExp()
		{
			int a = 5, b = 5;
			if (a == b || a == b) // [warn]: Left side of logical or is identical to right side.
				a = 6;
			if (a == b && a == b) // [warn]: Left side of logical and is identical to right side.
				a = 6;
		}
	}c, sac);

	assertAnalyzerWarningsDMD(q{
		void testAssignExp()
		{
			int a = 5, b = 5;
			a = b > 5 ? b : b; // [warn]: Left side of assignment operation is identical to the right side.
		}
	}c, sac);

	assertAnalyzerWarningsDMD(q{
		void foo()
		{
			if (auto stuff = call()) {}
		}
	}c, sac);

	stderr.writeln("Unittest for IfElseSameCheck passed.");
}
