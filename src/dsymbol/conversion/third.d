/**
 * This file is part of DCD, a development tool for the D programming language.
 * Copyright (C) 2014 Brian Schott
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

module dsymbol.conversion.third;

import dsymbol.conversion.second;
import dsymbol.semantic;
import dsymbol.string_interning;
import dsymbol.symbol;
import dsymbol.scope_;
import dsymbol.builtin.names;
import dsymbol.builtin.symbols;
import std.experimental.allocator;
import std.d.ast;
import std.d.lexer;

/**
 * Third pass handles the following:
 * $(UL
 *      $(LI types)
 *      $(LI base classes)
 *      $(LI mixin templates)
 *      $(LI alias this)
 *      $(LI alias declarations)
 * )
 */
struct ThirdPass
{
public:

	/**
	 * Params:
	 *     second = The second conversion pass. Results are taken from this to
	 *         run the third pass.
	 */
	this(ref SecondPass second) pure
	{
		this.rootSymbol = second.rootSymbol;
		this.moduleScope = second.moduleScope;
		this.symbolAllocator = second.symbolAllocator;
	}

	~this()
	{
		typeid(*rootSymbol).destroy(rootSymbol);
	}

	/**
	 * Runs the third pass.
	 */
	void run()
	{
		thirdPass(rootSymbol);
	}

	/**
	 * The module-level symbol
	 */
	SemanticSymbol* rootSymbol;

	/**
	 * The module-level scope
	 */
	Scope* moduleScope;

	/**
	 * The symbol allocator
	 */
	IAllocator symbolAllocator;

private:

	bool shouldFollowtype(const DSymbol* t, const SemanticSymbol* currentSymbol)
	{
		if (t is null)
			return false;
		if (currentSymbol.acSymbol.kind == CompletionKind.withSymbol
			&& (t.kind == CompletionKind.variableName
				|| t.kind == CompletionKind.aliasName))
		{
			return true;
		}
		if (t.kind == CompletionKind.aliasName)
			return true;
		return false;
	}

	void thirdPass(SemanticSymbol* currentSymbol)
	{
		with (CompletionKind) final switch (currentSymbol.acSymbol.kind)
		{
		case className:
		case interfaceName:
			resolveInheritance(currentSymbol);
			break;
		case withSymbol:
		case variableName:
		case memberVariableName:
		case functionName:
		case aliasName:
			DSymbol* t = resolveType(currentSymbol.initializer,
				currentSymbol.type, currentSymbol.acSymbol.location);
			while (shouldFollowtype(t, currentSymbol))
				t = t.type;
			currentSymbol.acSymbol.type = t;
			break;
		case structName:
		case unionName:
		case enumName:
		case keyword:
		case enumMember:
		case packageName:
		case moduleName:
		case dummy:
		case array:
		case assocArray:
		case templateName:
		case mixinTemplateName:
		case importSymbol:
			break;
		}

		foreach (child; currentSymbol.children)
		{
			thirdPass(child);
		}

		// Alias this and mixin templates are resolved after child nodes are
		// resolved so that the correct symbol information will be available.
		with (CompletionKind) switch (currentSymbol.acSymbol.kind)
		{
		case className:
		case interfaceName:
		case structName:
		case unionName:
			resolveAliasThis(currentSymbol);
			resolveMixinTemplates(currentSymbol);
			break;
		default:
			break;
		}
	}

	void resolveInheritance(SemanticSymbol* currentSymbol)
	{
		import std.algorithm : filter;
		outer: foreach (istring[] base; currentSymbol.baseClasses)
		{
			DSymbol* baseClass;
			if (base.length == 0)
				continue;
			auto symbolScope = moduleScope.getScopeByCursor(currentSymbol.acSymbol.location);
			auto symbols = moduleScope.getSymbolsByNameAndCursor(
				base[0], currentSymbol.acSymbol.location);
			if (symbols.length == 0)
				continue;
			baseClass = symbols[0];
			foreach (part; base[1..$])
			{
				symbols = baseClass.getPartsByName(part);
				if (symbols.length == 0)
					continue outer;
				baseClass = symbols[0];
			}
			foreach (_; baseClass.opSlice().filter!(a => a.name.ptr != CONSTRUCTOR_SYMBOL_NAME.ptr))
			{
				currentSymbol.acSymbol.addChild(_, false);
				symbolScope.symbols.insert(_);
			}
			if (baseClass.kind == CompletionKind.className)
			{
				auto s = make!DSymbol(symbolAllocator,
					SUPER_SYMBOL_NAME, CompletionKind.variableName, baseClass);
				symbolScope.symbols.insert(s);
			}
		}
	}

	void resolveAliasThis(SemanticSymbol* currentSymbol)
	{
		foreach (aliasThis; currentSymbol.aliasThis)
		{
			auto parts = currentSymbol.acSymbol.getPartsByName(aliasThis);
			if (parts.length == 0 || parts[0].type is null)
				continue;
			DSymbol* s = make!DSymbol(symbolAllocator, IMPORT_SYMBOL_NAME,
				CompletionKind.importSymbol);
			s.type = parts[0].type;
			currentSymbol.acSymbol.addChild(s, true);
		}
	}

	void resolveMixinTemplates(SemanticSymbol* currentSymbol)
	{
		foreach (mix; currentSymbol.mixinTemplates[])
		{
			auto symbols = moduleScope.getSymbolsByNameAndCursor(mix[0],
				currentSymbol.acSymbol.location);
			if (symbols.length == 0)
				continue;
			auto symbol = symbols[0];
			foreach (m; mix[1 .. $])
			{
				auto s = symbol.getPartsByName(m);
				if (s.length == 0)
				{
					symbol = null;
					break;
				}
				else
					symbol = s[0];
			}
			foreach (_; symbol.opSlice)
				currentSymbol.acSymbol.addChild(_, false);
		}
	}

	DSymbol* resolveInitializerType(I)(ref const I initializer, size_t location)
	{
		if (initializer.empty)
			return null;
		auto slice = initializer[];
		bool literal = slice.front[0] == '*';
		if (literal && initializer.length > 1)
		{
			slice.popFront();
			literal = false;
		}
		auto symbols = moduleScope.getSymbolsByNameAndCursor(internString(
			literal ? slice.front[1 .. $] : slice.front), location);

		if (symbols.length == 0)
			return null;

		if (literal)
			return symbols[0];

		slice.popFront();
		auto s = symbols[0];

		while (s !is null && s.type !is null && s !is s.type && !slice.empty)
		{
			s = s.type;
			if (slice.front == "foreach")
			{
				if (s.qualifier == SymbolQualifier.array)
					s = s.type;
				else
				{
					DSymbol*[] f = s.getPartsByName(internString("front"));
					if (f.length > 0)
						s = f[0].type;
					else
						s = null;
				}
				slice.popFront();
			}
			else if (slice.front == "[]")
				s = s.type;
			else
				break;
		}
		while (s !is null && !slice.empty)
		{
			auto parts = s.getPartsByName(internString(slice.front));
			if (parts.length == 0)
				return null;
			s = parts[0];
			slice.popFront();
		}
		return s;
	}

	DSymbol* resolveType(I)(ref const I initializer, const Type t, size_t location)
	{
		if (t is null)
			return resolveInitializerType(initializer, location);
		if (t.type2 is null)
			return null;
		DSymbol* s;
		if (t.type2.builtinType != tok!"")
			s = convertBuiltinType(t.type2);
		else if (t.type2.typeConstructor != tok!"")
			s = resolveType(initializer, t.type2.type, location);
		else if (t.type2.symbol !is null)
		{
			// TODO: global scoped symbol handling
			size_t l = t.type2.symbol.identifierOrTemplateChain.identifiersOrTemplateInstances.length;
			istring[] symbolParts = (cast(istring*) Mallocator.it.allocate(l * istring.sizeof))[0 .. l];
			scope(exit) Mallocator.it.deallocate(symbolParts);
			expandSymbol(symbolParts, t.type2.symbol.identifierOrTemplateChain);
			auto symbols = moduleScope.getSymbolsByNameAndCursor(
				symbolParts[0], location);
			if (symbols.length == 0)
				goto resolveSuffixes;
			s = symbols[0];
			foreach (symbolPart; symbolParts[1..$])
			{
				auto parts = s.getPartsByName(symbolPart);
				if (parts.length == 0)
					goto resolveSuffixes;
				s = parts[0];
			}
		}
	resolveSuffixes:
		foreach (suffix; t.typeSuffixes)
			s = processSuffix(s, suffix, t);
		return s;
	}

	static void expandSymbol(istring[] strings, const IdentifierOrTemplateChain chain)
	{
		for (size_t i = 0; i < chain.identifiersOrTemplateInstances.length; ++i)
		{
			auto identOrTemplate = chain.identifiersOrTemplateInstances[i];
			if (identOrTemplate is null)
			{
				strings[i] = istring(null);
				continue;
			}
			strings[i] = internString(identOrTemplate.templateInstance is null ?
				identOrTemplate.identifier.text
				: identOrTemplate.templateInstance.identifier.text);
		}
	}

	DSymbol* processSuffix(DSymbol* symbol, const TypeSuffix suffix, const Type t)
	{
		if (suffix.star.type != tok!"")
			return symbol;
		if (suffix.array || suffix.type)
		{
			DSymbol* s = make!DSymbol(symbolAllocator, istring(null));
			foreach (_; suffix.array ? arraySymbols[]: assocArraySymbols[])
				s.addChild(_, false);
			s.type = symbol;
			s.qualifier = suffix.array ? SymbolQualifier.array : SymbolQualifier.assocArray;
			return s;
		}
		if (suffix.parameters)
		{
			import dsymbol.conversion.first : formatNode;
			import std.array : appender;
			DSymbol* s = make!DSymbol(symbolAllocator, istring(null));
			s.type = symbol;
			s.qualifier = SymbolQualifier.func;
			auto app = appender!(char[]);
			app.formatNode(t);
			s.callTip = internString(cast(string) app.data);
			return s;
		}
		return null;
	}

	DSymbol* convertBuiltinType(const Type2 type2)
	{
		istring stringRepresentation = getBuiltinTypeName(type2.builtinType);
		DSymbol s = DSymbol(stringRepresentation);
		assert(s.name.ptr == stringRepresentation.ptr);
		return builtinSymbols.equalRange(&s).front();
	}
}
