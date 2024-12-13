//          Copyright Brian Schott (Hackerpilot) 2015.
// Distributed under the Boost Software License, Version 1.0.
//    (See accompanying file LICENSE_1_0.txt or copy at
//          http://www.boost.org/LICENSE_1_0.txt)
module dscanner.analysis.unmodified;

import dscanner.analysis.base;
import dscanner.analysis.nolint;
import dscanner.utils : safeAccess;
import dsymbol.scope_ : Scope;
import std.container;
import dparse.ast;
import dparse.lexer;

/**
 * Checks for variables that could have been declared const or immutable
 */
// TODO: many similarities to unused_param.d, maybe refactor into a common base class
extern (C++) class UnmodifiedFinder(AST) : BaseAnalyzerDmd
{
	alias visit = BaseAnalyzerDmd.visit;
	mixin AnalyzerInfo!"could_be_immutable_check";

	private enum KEY = "dscanner.suspicious.unmodified";
	private enum MSG = "Variable %s is never modified and could have been declared const or immutable.";

	override void visit(const Module mod)
	{
		pushScope();
		mod.accept(this);
		popScope();
	}

	override void visit(const BlockStatement blockStatement)
	{
		pushScope();
		blockStatementDepth++;
		blockStatement.accept(this);
		blockStatementDepth--;
		popScope();
	}

	override void visit(const StructBody structBody)
	{
		pushScope();
		immutable oldBlockStatementDepth = blockStatementDepth;
		blockStatementDepth = 0;
		structBody.accept(this);
		blockStatementDepth = oldBlockStatementDepth;
		popScope();
	}

	override void visit(const VariableDeclaration dec)
	{
		if (dec.autoDeclaration is null && blockStatementDepth > 0
				&& isImmutable <= 0 && !canFindImmutable(dec))
		{
			foreach (d; dec.declarators)
			{
				if (initializedFromCast(d.initializer))
					continue;
				if (initializedFromNew(d.initializer))
					continue;
				tree[$ - 1].insert(new VariableInfo(d.name.text, d.name, isValueTypeSimple(dec.type)));
			}
		}
		dec.accept(this);
	}

	override void visit(const AutoDeclaration autoDeclaration)
	{
		import std.algorithm : canFind;

		if (blockStatementDepth > 0 && isImmutable <= 0
				&& (!autoDeclaration.storageClasses.canFind!(a => a.token == tok!"const"
					|| a.token == tok!"enum" || a.token == tok!"immutable")))
		{
			foreach (part; autoDeclaration.parts)
			{
				if (initializedFromCast(part.initializer))
					continue;
				if (initializedFromNew(part.initializer))
					continue;
				tree[$ - 1].insert(new VariableInfo(part.identifier.text, part.identifier));
			}
		}
		autoDeclaration.accept(this);
	}

	override void visit(const AssignExpression assignExpression)
	{
		if (assignExpression.operator != tok!"")
		{
			interest++;
			guaranteeUse++;
			assignExpression.ternaryExpression.accept(this);
			guaranteeUse--;
			interest--;

			if (assignExpression.operator == tok!"~=")
				interest++;
			assignExpression.expression.accept(this);
			if (assignExpression.operator == tok!"~=")
				interest--;
		}
		else
			assignExpression.accept(this);
	}

	override void visit(const Declaration dec)
	{
		if (canFindImmutableOrConst(dec))
		{
			isImmutable++;
			with (noLint.push(NoLintFactory.fromDeclaration(dec)))
				dec.accept(this);
			isImmutable--;
		}
		else
		{
			with (noLint.push(NoLintFactory.fromDeclaration(dec)))
				dec.accept(this);
		}
	}

	override void visit(const IdentifierChain ic)
	{
		if (ic.identifiers.length && interest > 0)
			variableMightBeModified(ic.identifiers[0].text);
		ic.accept(this);
	}

	override void visit(const IdentifierOrTemplateInstance ioti)
	{
		if (ioti.identifier != tok!"" && interest > 0)
			variableMightBeModified(ioti.identifier.text);
		ioti.accept(this);
	}

	mixin PartsMightModify!AsmPrimaryExp;
	mixin PartsMightModify!IndexExpression;
	mixin PartsMightModify!FunctionCallExpression;
	mixin PartsMightModify!NewExpression;
	mixin PartsMightModify!IdentifierOrTemplateChain;
	mixin PartsMightModify!ReturnStatement;

	override void visit(const UnaryExpression unary)
	{
		if (unary.prefix == tok!"++" || unary.prefix == tok!"--"
				|| unary.suffix == tok!"++" || unary.suffix == tok!"--"
				|| unary.prefix == tok!"*" || unary.prefix == tok!"&")
		{
			interest++;
			guaranteeUse++;
			unary.accept(this);
			guaranteeUse--;
			interest--;
		}
		else
			unary.accept(this);
	}

	override void visit(const ForeachStatement foreachStatement)
	{
		if (foreachStatement.low !is null)
		{
			interest++;
			foreachStatement.low.accept(this);
			interest--;
		}
		if (foreachStatement.declarationOrStatement !is null)
			foreachStatement.declarationOrStatement.accept(this);
	}

	override void visit(const TraitsExpression)
	{
		// issue #266: Ignore unmodified variables inside of `__traits` expressions
	}

	override void visit(const TypeofExpression)
	{
		// issue #270: Ignore unmodified variables inside of `typeof` expressions
	}

	override void visit(const AsmStatement a)
	{
		inAsm = true;
		a.accept(this);
		inAsm = false;
	}

private:

	enum string KEY = "dscanner.suspicious.unmodified";

	template PartsMightModify(T)
	{
		override void visit(const T t)
		{
			interest++;
			t.accept(this);
			interest--;
		}
	}

	void variableMightBeModified(string name)
	{
		size_t index = tree.length - 1;
		auto vi = VariableInfo(name);
		if (guaranteeUse == 0)
		{
			auto r = tree[index].equalRange(&vi);
			if (!r.empty && r.front.isValueType && !inAsm)
				return;
		}
		while (true)
		{
			if (tree[index].removeKey(&vi) != 0 || index == 0)
				break;
			index--;
		}
	}

	bool initializedFromNew(const Initializer initializer)
	{
		if (const UnaryExpression ue = cast(UnaryExpression) safeAccess(initializer)
			.nonVoidInitializer.assignExpression)
		{
			return ue.newExpression !is null;
		}
		return false;
	}

	bool initializedFromCast(const Initializer initializer)
	{
		import std.typecons : scoped;

		static class CastFinder : ASTVisitor
		{
			alias visit = ASTVisitor.visit;
			override void visit(const CastExpression castExpression)
			{
				foundCast = true;
				castExpression.accept(this);
			}

			bool foundCast;
		}

		if (initializer is null)
			return false;
		auto finder = scoped!CastFinder();
		finder.visit(initializer);
		return finder.foundCast;
	}

	bool canFindImmutableOrConst(const Declaration dec)
	{
		import std.algorithm : canFind, map, filter;

		return !dec.attributes.map!(a => a.attribute)
			.filter!(a => a == tok!"immutable" || a == tok!"const").empty;
	}

	bool canFindImmutable(const VariableDeclaration dec)
	{
		import std.algorithm : canFind;

		foreach (storageClass; dec.storageClasses)
		{
			if (storageClass.token == tok!"enum")
				return true;
		}
		foreach (sc; dec.storageClasses)
		{
			if (sc.token == tok!"immutable" || sc.token == tok!"const")
				return true;
		}
		if (dec.type !is null)
		{
			foreach (tk; dec.type.typeConstructors)
				if (tk == tok!"immutable" || tk == tok!"const")
					return true;
			if (dec.type.type2)
			{
				const tk = dec.type.type2.typeConstructor;
				if (tk == tok!"immutable" || tk == tok!"const")
					return true;
			}
		}
		return false;
	}

	static struct VariableInfo
	{
		string name;
		ulong lineNum;
		ulong charNum;
		bool isUsed = false;
	}

	private alias VarSet = VarInfo[string];
	private VarSet[] usedVars;
	private bool inAggregate;

	extern (D) this(string fileName, bool skipTests = false)
	{
		super(fileName, skipTests);
		pushScope();
	}

	override void visit(AST.UserAttributeDeclaration userAttribute)
	{
		if (shouldIgnoreDecl(userAttribute, KEY))
			return;

		super.visit(userAttribute);
	}

	override void visit(AST.Module mod)
	{
		if (shouldIgnoreDecl(mod.userAttribDecl(), KEY))
			return;

		super.visit(mod);
	}

	override void visit(AST.CompoundStatement compoundStatement)
	{
		pushScope();
		super.visit(compoundStatement);
		popScope();
	}

	override void visit(AST.TemplateDeclaration templateDeclaration)
	{
		auto oldInTemplate = inAggregate;
		inAggregate = true;
		super.visit(templateDeclaration);
		inAggregate = oldInTemplate;
	}

	override void visit(AST.StructDeclaration structDecl)
	{
		auto oldInAggregate = inAggregate;
		inAggregate = true;
		super.visit(structDecl);
		inAggregate = oldInAggregate;
	}

	override void visit(AST.VarDeclaration varDeclaration)
	{
		import dmd.astenums : STC;

		super.visit(varDeclaration);

		if (varDeclaration.ident is null)
			return;

		string varName = cast(string) varDeclaration.ident.toString();
		bool isConst = varDeclaration.storage_class & STC.const_ || varDeclaration.storage_class & STC.immutable_
			|| varDeclaration.storage_class & STC.manifest || isConstType(varDeclaration.type);

		bool markAsUsed = isConst || isFromCastOrNew(varDeclaration._init) || inAggregate;
		currentScope[varName] = VarInfo(varName, varDeclaration.loc.linnum, varDeclaration.loc.charnum, markAsUsed);
	}

	private bool isConstType(AST.Type type)
	{
		import dmd.astenums : MODFlags;

		if (type is null)
			return false;

		bool isConst = type.mod & MODFlags.const_ || type.mod & MODFlags.immutable_;

		if (auto typePtr = type.isTypePointer())
			isConst = isConst || typePtr.next.mod & MODFlags.const_ || typePtr.next.mod & MODFlags.immutable_;

		return isConst;
	}

	private bool isFromCastOrNew(AST.Initializer initializer)
	{
		if (initializer is null)
			return false;

		auto initExpr = initializer.isExpInitializer();
		if (initExpr is null)
			return false;

		return initExpr.exp.isNewExp() !is null || initExpr.exp.isCastExp() !is null;
	}

	override void visit(AST.IntervalExp intervalExp)
	{
		super.visit(intervalExp);

		auto identifier1 = intervalExp.lwr.isIdentifierExp();
		if (identifier1 && identifier1.ident)
			markAsUsed(cast(string) identifier1.ident.toString());

		auto identifier2 = intervalExp.upr.isIdentifierExp();
		if (identifier2 && identifier2.ident)
			markAsUsed(cast(string) identifier2.ident.toString());
	}

	override void visit(AST.IndexExp indexExpression)
	{
		super.visit(indexExpression);

		auto identifier1 = indexExpression.e1.isIdentifierExp();
		if (identifier1 && identifier1.ident)
			markAsUsed(cast(string) identifier1.ident.toString());

		auto identifier2 = indexExpression.e2.isIdentifierExp();
		if (identifier2 && identifier2.ident)
			markAsUsed(cast(string) identifier2.ident.toString());
	}

	mixin VisitAssignNode!(AST.AssignExp);
	mixin VisitAssignNode!(AST.BinAssignExp);
	mixin VisitAssignNode!(AST.PtrExp);
	mixin VisitAssignNode!(AST.AddrExp);
	mixin VisitAssignNode!(AST.PreExp);
	mixin VisitAssignNode!(AST.PostExp);

	private template VisitAssignNode(NodeType)
	{
		override void visit(NodeType node)
		{
			immutable string errorMessage = "Variable " ~ vi.name
				~ " is never modified and could have been declared const or immutable.";
			addErrorMessage(vi.token, KEY, errorMessage);
		}
	}

	mixin VisitFunctionNode!(AST.CallExp);
	mixin VisitFunctionNode!(AST.NewExp);

	private template VisitFunctionNode(NodeType)
	{
		override void visit(NodeType node)
		{
			super.visit(node);

			if (node.arguments is null)
				return;

			foreach (arg; *node.arguments)
			{
				auto identifier = arg.isIdentifierExp();
				if (identifier && identifier.ident)
					markAsUsed(cast(string) arg.isIdentifierExp().ident.toString());
			}
		}
	}

	mixin VisitDotExpressionNode!(AST.DotIdExp);
	mixin VisitDotExpressionNode!(AST.DotTemplateInstanceExp);

	private template VisitDotExpressionNode(NodeType)
	{
		override void visit(NodeType node)
		{
			super.visit(node);
			auto identifierExp = node.e1.isIdentifierExp();
			if (identifierExp && identifierExp.ident)
				markAsUsed(cast(string) identifierExp.ident.toString());
		}
	}

	private extern (D) void markAsUsed(string varName)
	{
		import std.range : retro;

		foreach (funcScope; usedVars.retro())
		{
			if (varName in funcScope)
			{
				funcScope[varName].isUsed = true;
				break;
			}
		}
	}

	@property private extern (D) VarSet currentScope()
	{
		return usedVars[$ - 1];
	}

	private void pushScope()
	{
		// Error with gdc-12
		//usedVars ~= new VarSet;

		// Workaround for gdc-12
		VarSet newScope;
		newScope["test"] = VarInfo("test", 0, 0);
		usedVars ~= newScope;
		currentScope.remove("test");
	}

	private void popScope()
	{
		import std.algorithm : each, filter;
		import std.format : format;

		currentScope.byValue
			.filter!(var => !var.isUsed)
			.each!(var => addErrorMessage(var.lineNum, var.charNum, KEY, MSG.format(var.name)));

		usedVars.length--;
	}
}

unittest
{
	import dscanner.analysis.config : StaticAnalysisConfig, Check, disabledConfig;
	import dscanner.analysis.helpers : assertAnalyzerWarningsDMD;
	import std.stdio : stderr;

	StaticAnalysisConfig sac = disabledConfig();
	sac.could_be_immutable_check = Check.enabled;

	// fails
	assertAnalyzerWarningsDMD(q{
		void foo()
		{
			int i = 1; // [warn]: Variable i is never modified and could have been declared const or immutable.
		}
	}, sac);

	assertAnalyzerWarningsDMD(q{
		void foo()
		{
			int i = 5; // [warn]: Variable i is never modified and could have been declared const or immutable.
			int j = 6;
			j = i + 5;
		}
	}c, sac);

	// pass
	assertAnalyzerWarningsDMD(q{
		void foo()
		{
			const(int) i;
			const int j;
			const(int)* a;
			const int* b;
		}
	}, sac);

	assertAnalyzerWarningsDMD(q{
		void foo()
		{
			immutable(int) i;
			immutable int j;
			immutable(int)* b;
			immutable int* a;
		}
	}, sac);

	assertAnalyzerWarningsDMD(q{
		void foo()
		{
			enum i = 1;
			enum string j = "test";
		}
	}, sac);

	assertAnalyzerWarningsDMD(q{
		void foo()
		{
			E e = new E;
			auto f = new F;
		}
	}, sac);

	assertAnalyzerWarningsDMD(q{
		void issue640()
		{
			size_t i1;
			new Foo(i1);

			size_t i2;
			foo(i2);
		}
	}, sac);

	assertAnalyzerWarnings(q{
		@("nolint(dscanner.suspicious.unmodified)")
		void foo(){
			int i = 1;
		}
	}, sac);
}

	assertAnalyzerWarningsDMD(q{
		void foo()
		{
			int i = 5; // [warn]: Variable i is never modified and could have been declared const or immutable.
			int j = 6;
			j = i + 5;
		}
	}c, sac);

	assertAnalyzerWarningsDMD(q{
		void foo()
		{
			int i = 5;
			if (true)
				--i;
			else
				i++;
		}
	}c, sac);

	assertAnalyzerWarningsDMD(q{
		@("nolint(dscanner.suspicious.unmodified)")
		void foo(){
			int i = 1;
		}
	}, sac);

	stderr.writeln("Unittest for UnmodifiedFinder passed.");
}
