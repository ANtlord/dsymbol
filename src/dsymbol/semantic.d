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

module dsymbol.semantic;

import dsymbol.symbol;
import std.d.ast;
import std.d.lexer;
import containers.unrolledlist;

/**
 * Intermediate form between DSymbol and the AST classes. Stores enough
 * information to resolve things like base classes and alias this.
 */
struct SemanticSymbol
{
public:

	/// Disable default construction.
	@disable this();
	/// Disable copy construction
	@disable this(this);

	/**
	 * Params:
	 *    name = the name
	 *    kind = the completion kind
	 *    symbolFile = the file name for this symbol
	 *    location = the location of this symbol
	 */
	this(DSymbol* acSymbol, const Type type = null)
	{
		this.acSymbol = acSymbol;
		this.type = type;
	}

	~this()
	{
		foreach (child; children[])
			typeid(SemanticSymbol).destroy(child);
	}

	/**
	 * Adds a child to the children field and updates the acSymbol's parts field
	 */
	void addChild(SemanticSymbol* child, bool owns)
	{
		children.insert(child);
		acSymbol.addChild(child.acSymbol, owns);
	}

	/// Autocompletion symbol
	DSymbol* acSymbol;

	/// Base classes
	UnrolledList!(istring[]) baseClasses;

	/// Variable type or function return type
	const Type type;

	/// Alias this symbols
	UnrolledList!(istring) aliasThis;

	/// MixinTemplates
	UnrolledList!(istring[]) mixinTemplates;

	/// Protection level for this symobol
	IdType protection;

	/// Parent symbol
	SemanticSymbol* parent;

	/// Child symbols
	UnrolledList!(SemanticSymbol*) children;

	/// Assign expression identifier chain used for auto declarations
	UnrolledList!(istring) initializer;
}

/**
 * Type of the _argptr variable
 */
Type argptrType;

/**
 * Type of _arguments
 */
Type argumentsType;

static this()
{
	import dsymbol.string_interning : internString;
	import std.experimental.allocator : make;
	import std.experimental.allocator.mallocator : Mallocator;

	// _argptr has type void*
	argptrType = make!Type(Mallocator.it);
	argptrType.type2 = make!Type2(Mallocator.it);
	argptrType.type2.builtinType = tok!"void";
	TypeSuffix argptrTypeSuffix = make!TypeSuffix(Mallocator.it);
	argptrTypeSuffix.star = Token(tok!"*");
	argptrType.typeSuffixes = cast(TypeSuffix[]) Mallocator.it.allocate(TypeSuffix.sizeof);
	argptrType.typeSuffixes[0] = argptrTypeSuffix;

	// _arguments has type TypeInfo[]
	argumentsType = make!Type(Mallocator.it);
	argumentsType.type2 = make!Type2(Mallocator.it);
	argumentsType.type2.symbol = make!Symbol(Mallocator.it);
	argumentsType.type2.symbol.identifierOrTemplateChain = make!IdentifierOrTemplateChain(Mallocator.it);
	IdentifierOrTemplateInstance i = make!IdentifierOrTemplateInstance(Mallocator.it);
	i.identifier.text = internString("TypeInfo");
	i.identifier.type = tok!"identifier";
	argumentsType.type2.symbol.identifierOrTemplateChain.identifiersOrTemplateInstances =
		cast(IdentifierOrTemplateInstance[]) Mallocator.it.allocate(IdentifierOrTemplateInstance.sizeof);
	argumentsType.type2.symbol.identifierOrTemplateChain.identifiersOrTemplateInstances[0] = i;
	TypeSuffix argumentsTypeSuffix = make!TypeSuffix(Mallocator.it);
	argumentsTypeSuffix.array = true;
	argumentsType.typeSuffixes = cast(TypeSuffix[]) Mallocator.it.allocate(TypeSuffix.sizeof);
	argumentsType.typeSuffixes[0] = argumentsTypeSuffix;
}
