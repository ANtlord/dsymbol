module dsymbol.conversion.resolve.from_initializer;

import dsymbol.string_interning : internString;
import dsymbol.symbol : DSymbol;
import dsymbol.symbol : CompletionKind;
import dsymbol.symbol : SymbolQualifier;
import dsymbol.scope_ : Scope;
import dsymbol.builtin.names : symbolNameToTypeName;
import dsymbol.builtin.names : ARRAY_SYMBOL_NAME;
import dsymbol.builtin.symbols : arraySymbols;
import dsymbol.type_lookup : TypeLookup;
import dsymbol.modulecache : ModuleCache;
import std.experimental.allocator : make;
import std.experimental.allocator : IAllocator;
import dsymbol.string_interning : istring;

/**
 * Determine type of variable using lookup breadcrumbs.
 *
 * Params:
 * 	symbol =		contains list of words used for completions of variable. Will be used as return value.
 * 	lookup =		contains information collected from initialization of variable.
 * 	moduleScope = 	allows to find symbols in files by cursor position.
 * 	cache =			reference to cache of module used for getting prepared last
 * 					suffix or make it. It cannot be constant because its
 * 					allocator allocates memory for last suffix.
 *
 * Returns: nothing.
 */
void resolveTypeFromInitializer(DSymbol* symbol, in TypeLookup* lookup,
	in Scope* moduleScope, ref ModuleCache cache)
{
	if (lookup.breadcrumbs.length == 0)
		return;
	DSymbol* currentSymbol = null;
	size_t i = 0;

	auto crumbs = lookup.breadcrumbs[];
	foreach (crumb; crumbs)
	{
		if (i == 0)
		{
			currentSymbol = moduleScope.getFirstSymbolByNameAndCursor(
				symbolNameToTypeName(crumb), symbol.location);

			// solves auto arrays
			if (crumb == ARRAY_SYMBOL_NAME)
			{
				auto nestedArr = crumbs.save();
				istring a = nestedArr.front();

				DSymbol* suffix;
				DSymbol* lastSuffix;

				// process the flags set in ArrayInitializer visit
				int count;
				while (true)
				{
					lastSuffix = cache.symbolAllocator.make!(DSymbol)(a, CompletionKind.dummy, lastSuffix);
					lastSuffix.qualifier = SymbolQualifier.array;

					if (suffix is null)
						suffix = lastSuffix;

					nestedArr.popFront();
					if (nestedArr.empty())
						break;
					a = nestedArr.front();
					if (a != ARRAY_SYMBOL_NAME)
						break;
				}

				// last crumb should be the element type
				DSymbol* elemType;
				if (!nestedArr.empty)
				{
					suffix.addChildren(arraySymbols[], false);
					elemType = moduleScope.getFirstSymbolByNameAndCursor(
						symbolNameToTypeName(a), symbol.location);
				}

				// put the elem type to the back of the *arr* chain
				if (suffix !is null && elemType)
				{
					suffix.type = elemType;
					suffix.ownType = false;
					symbol.type = lastSuffix;
					symbol.ownType = true;
				}
			}
			if (currentSymbol is null)
				return;
		}
		else if (crumb == ARRAY_SYMBOL_NAME)
		{
			typeSwap(currentSymbol);
			if (currentSymbol is null)
				return;

			// Index expressions can be an array index or an AA index
			if (currentSymbol.qualifier == SymbolQualifier.array
					|| currentSymbol.qualifier == SymbolQualifier.assocArray
					|| currentSymbol.kind == CompletionKind.aliasName)
			{
				if (currentSymbol.type !is null)
					currentSymbol = currentSymbol.type;
				else
					return;
			}
			else
			{
				auto opIndex = currentSymbol.getFirstPartNamed(internString("opIndex"));
				if (opIndex !is null)
					currentSymbol = opIndex.type;
				else
					return;
			}
		}
		else if (crumb == "foreach")
		{
			typeSwap(currentSymbol);
			if (currentSymbol is null)
				return;
			if (currentSymbol.qualifier == SymbolQualifier.array
					|| currentSymbol.qualifier == SymbolQualifier.assocArray)
			{
				currentSymbol = currentSymbol.type;
				break;
			}
			auto front = currentSymbol.getFirstPartNamed(internString("front"));
			if (front !is null)
			{
				currentSymbol = front.type;
				break;
			}
			auto opApply = currentSymbol.getFirstPartNamed(internString("opApply"));
			if (opApply !is null)
			{
				currentSymbol = opApply.type;
				break;
			}
		}
		else
		{
			typeSwap(currentSymbol);
			if (currentSymbol is null )
				return;
			currentSymbol = currentSymbol.getFirstPartNamed(crumb);
		}
		++i;
		if (currentSymbol is null)
			return;
	}
	typeSwap(currentSymbol);
	symbol.type = currentSymbol;
	symbol.ownType = false;
}

unittest
{
	import dsymbol.type_lookup : TypeLookupKind;
	import dsymbol.modulecache : ASTAllocator;
	import std.stdio : writeln;
	import std.algorithm.iteration : reduce;
	import std.algorithm.iteration : map;
	import std.conv : to;
	import std.c.process;

	T[][] comb(T)(in T[] arr, in int k) pure nothrow {
		if (k == 0) return [[]];
		typeof(return) result;
		foreach (immutable i, immutable x; arr)
			foreach (suffix; arr[i + 1 .. $].comb(k - 1))
				result ~= x ~ suffix;
		return result;
	}

	struct Fixture {
		static Fixture opCall() {
			auto lookupKind = TypeLookupKind.initializer;
			Fixture obj = {
				new DSymbol(istring("somevar")),
				new TypeLookup(lookupKind),
				new Scope(0, 0),
				ModuleCache(new ASTAllocator)
			};

			return obj;
		}

		DSymbol * symbol;
		TypeLookup * lookup;
		Scope * moduleScope;
		ModuleCache cache;
	}

	// Fixture[] buildFixture(DSymbol*[], TypeLookup*[], Scope*[], ModuleCache[])
	// {
		
	// }

	struct Test {
		int a;
		string qwe;
	}

	struct Counter {
		this(ulong[] in_lens)
		in
		{
			assert(in_lens.length > 0);
		}
		body 
		{
			foreach(i, elem; in_lens)
			{
				_lens ~= elem;
				++_chainCount;
				if (i == 0LU) {
					this.chain = new ChainIndex(elem);
				}
				else {
					this.chain.add(new ChainIndex(elem));
				}
			}
		}

		struct ChainIndex {
			this(ulong max) {
				_max = max;
			}

			void add(ChainIndex * next) {
				if (_next is null) {
					_next = next;
				}
				else {
					_next.add(next);
				}
			}

			ref ChainIndex opUnary(string op)() {
				if (op == "++") {
					if(_val < _max) {
						++_val;
					}
					else {
						_val = 0;
						if (_next !is null) {
							++(*_next);
						}
					}
					return this;
				}
			}

			ulong[] vals()
			{
				ulong[] res = [this._val];
				ChainIndex * curIndex = this._next;

				while (curIndex !is null) {
					res ~= curIndex._val;
					curIndex = curIndex._next;
				}
				return res;
			}

			private:
				ulong _val = 0;
				ulong _max = 0;
				ChainIndex * _next = null;

		}

		ref ulong[] lens() {
			return _lens;
		}

		ulong[] vals()
		{
			auto vals = this.chain.vals();
			return vals;
		}

		private:
			ulong[] _lens = [];
			int _chainCount = 0;
			ChainIndex * chain = null;
	}
	
	O[] factory(O, Args ...)(Args args) 
	{
		O[] arr;
		ulong[] lens;
		foreach(elem; args)
		{
			lens ~= elem.length;
		}
		auto counter = Counter(lens);
		writeln(counter.vals);
		++(*counter.chain);
		writeln(counter.vals);
		++(*counter.chain);
		writeln(counter.vals);
		++(*counter.chain);
		writeln(counter.vals);

		// const int count = 0;
		// static auto args_ = args;
		// for (size_t i = 0; i < Args.length; ++i)
		// {
			// pragma(msg, i);
		// }
		// static if (args.length > 0) {
			// pragma(msg, args[0]);
		// }
		// foreach(arg; args) {
			// pragma(msg, arg);
			// mixin("writeln(" ~ to!(string)(i) ~ ");");
			// // auto nextLevel = to!string(depthLevel + 1);
			// // auto currentLevel = to!string(depthLevel);
			// // mixin("foreach(arg" ~ nextLevel ~ "; arg" ~ currentLevel ~ ") writeln(arg" ~ currentLevel~ ");");
			// // count++;
		// }
		return arr;
	}

	template fun(T...)
	{
		static void _func()
		in {
			foreach(i, elem; T)
			{
				static assert(T[i].length > 0);
			}
		}
		body
		{
			foreach(i, elem0; T) {
				enum level = to!string(i);
				enum nextLevel = to!string(i + 1);
				// mixin(`foreach(elem` ~ nextLevel ~ `; elem ` ~ level ~ `);`);
			}
		}

		alias fun = _func;
		// pragma(msg, T[0]);
		// void fun(QQ arg) {
			// static var = arg;
			// // static assert(typeof(arg) == int)
			// // pragma(msg, arg);
		// }
		// int fun(O outType, Args args)
		// {
			// return 1;
		// }
	}

	{
		alias qwe = fun!([1], [1, 2]);
		// writeln(qwe);
		auto objs = factory!(Test, int[], string[])([3], ["3.13"]);
		// writeln("Test without any breadcrumb in lookup.");
		// auto fixture = Fixture();
		// auto symbol = fixture.symbol;
		// resolveTypeFromInitializer(symbol, fixture.lookup, fixture.moduleScope, fixture.cache);
		// assert(symbol.type is null);
		// assert(symbol.ownType == false);
	}

	// {
		// writeln("Test with one breadcrumb in lookup.");
		// auto fixture = Fixture();
		// auto symbol = fixture.symbol;
		// resolveTypeFromInitializer(symbol, fixture.lookup, fixture.moduleScope, fixture.cache);
		// assert(symbol.type is null);
		// assert(symbol.ownType == false);
	// }
}

void typeSwap(ref DSymbol* currentSymbol)
{
	while (currentSymbol !is null && currentSymbol.type !is currentSymbol
			&& (currentSymbol.kind == CompletionKind.variableName
			|| currentSymbol.kind == CompletionKind.importSymbol
			|| currentSymbol.kind == CompletionKind.withSymbol
			|| currentSymbol.kind == CompletionKind.aliasName))
		currentSymbol = currentSymbol.type;
}
