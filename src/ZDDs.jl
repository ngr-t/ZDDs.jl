"""
ZDDs.jl
===

Implementation of ZDD (Zero-supressed Binary Decision Diagram) proposed by Shin-ichi Minato.
ZDD is a data structure which represents combination sets (family).

The operations below are supported:

- empty
- base
- subset0
- subset1
- change
- intersect
- union
- setdiff

example:
```julia
julia> using ZDDs
julia> zdd1 = tozdd(((1,), (1, 2)))
julia> zdd2 = tozdd(((2,), (1, 2), (2, 3, 4)))

julia> tofamily(union(zdd1, zdd2))
Set([Set([1]),Set([2,1]),Set([2]),Set([4,2,3])])

julia> tofamily(setdiff(zdd1, zdd2))
Set([Set([1])])

julia> tofamily(setdiff(zdd2, zdd1))
Set([Set([2]),Set([4,2,3])])

julia> tofamily(intersect(zdd1, zdd2))
Set([Set([2,1])])
```


reference:
Minato, S, 2001, Zero-suppressed BDDs and their applications, 
International Journal on Software Tools for Technology

"""

module ZDDs

import Base.union
import Base.isempty
import Base.first
import Base.intersect
import Base.setdiff
import Base.length

export 
	ZDD,
	tozdd,
	setdiff,
	intersect,
	union,
	tofamily,
	print_size,
	subset0,
	subset1,
	change,
	clear_caches!


"""
Node type
===
The type representing nodes, of which ZDDs are comprised.
Node type has 3 fields:

- top::Int
- child0::Node
- child1::Node
"""
mutable struct Node
	# label value 
	top::Int
	# reference to the root node of the partial graph
	# representing combination sets which don't include *top*s.
	child0::Node
	# reference to the root node of the partial graph
	# representing combination sets which include *top*s.
	child1::Node

	function Node()
		new_node = new()
		new_node.child0 = new_node
		new_node.child1 = new_node
		return new_node
	end
	"""
	This constructor makes an instance with circular references to itself.
	Intented to used as constructor of "terminal" nodes.
	"""
	function Node(top::Int)
		new_node = new()
		new_node.top = top
		new_node.child0 = new_node
		new_node.child1 = new_node
		return new_node
	end

	"""
	This constructor makes an instance with the top value and
	the references to child nodes as given args.
	"""
	function Node(top::Int, child0::Node, child1::Node)
		new_node = new()
		new_node.top = top
		new_node.child0 = child0
		new_node.child1 = child1
		return new_node
	end
end


# Define terminal nodes.
# It is another considerable (and maybe safer) choice to define *Node* as an abstract type
# and to separate terminal nodes and normal nodes into different derived types.
# I thought that defining *Node* as a concrete type is better in view of performance,
# but I've not yet compared the performances of each versions.

# The top values of the terminal nodes are not referenced.

# The true terminal node.
const true_terminal = Node(typemin(Int))

# The false terminal node.
const false_terminal = Node(typemax(Int))


"""
ZDD type
"""
mutable struct ZDD
	root::Node
end

"""
returns an empty ZDD (which represents an empty combination set)
"""
function emptyzdd()
	return ZDD(false_terminal)
end


"""
returns a base ZDD (which represents a combination set with only an empty combination)
"""
function basezdd()
	return ZDD(true_terminal)
end

"""
main recursive function of tofamily
"""
function tofamily_sub_zdd(node::Node)
	if isempty(node)
		return Set{Set{Int}}()
	elseif isbase(node)
		return Set([Set{Int}([])])
	end
	child0 = tofamily_sub_zdd(node.child0)
	child1 = tofamily_sub_zdd(node.child1)
	for set in child1 
		push!(set, node.top)
	end
	return union(child0, child1)
end

"""
Convert the combination set represented by *ZDD* into *Set{Set{Int}}*.
"""
function tofamily(zdd::ZDD)
	tofamily_sub_zdd(zdd.root)
end

"""
Array with the position currently referenced.
It is used in tozdd_sub! function.
"""
mutable struct ArrayWithPos{V <: AbstractVector{Int}}
	parent::V
	pos::Int
end

"""Returns true if *pos* of *arr* is over the length of *arr*."""
isempty(arr::ArrayWithPos) = ! (arr.pos <= length(arr.parent))

"""Get the element at *pos* from *arr*."""
first(arr::ArrayWithPos) = arr.parent[arr.pos]

"""Increment *pos* of *arr*."""
function inc!(arr::ArrayWithPos)
	arr.pos += 1
end

"""Decrement *pos* of *arr*."""
function dec!(arr::ArrayWithPos)
	arr.pos -= 1
end

"""
main recursive function of tozdd
"""
function tozdd_sub!(family)
	if isempty(family)
		return false_terminal
	elseif length(family) == 1
		if isempty(first(family))
			return true_terminal
		end
	end

	# Search the maximum value in *family*.
	# *s*s in *family* are already sorted, so checking the first values is enough.
	top = typemin(Int)
	for s in family
		if ! isempty(s)
			top = max(top, first(s))
		end
	end

	# The ver. commented out below is slower than the ver. upon (due to memory allocation within *filter* function)
	# top = mapreduce(first, max, filter(s -> !isempty(s), family))

	# Sort *family* in-place by the condition whether *s* includes *top*.
	# The reason not to use *sort* function is
	#   1) to sort *family* and 
	#   2) to get the index of the first combination which includes *top* in sorted family
	# by one-path.
	f = 1
	e = length(family)
	while f < e
		sf = family[f]
		se = family[e]
		if isempty(sf) || first(sf) != top
			f += 1
		else
			if isempty(se) || first(se) != top
				family[f] = family[e]
				family[e] = sf
			else
				e -= 1
			end
		end
	end
	# At the end of the loop, each element in *family[1:f-1]* does not include *top*,
	# and that in *family[f:length(family)]* includes *top*.

	# Create *SubArray*s.
	f0 = view(family, 1:f-1)
	f1 = view(family, f:length(family))

	# Increment every *pos* of *s*s in *f1*.
	# After the incrementation, the values in *arr* with index larger than *pos*
	# are less than *top*.
	for s in f1
		inc!(s)
	end
	# Construct sub-ZDDs representing *f0* and *f1*.
	child0 = tozdd_sub!(f0)
	child1 = tozdd_sub!(f1)

	# After sub-ZDDs are constructed, get back *s*s in *f1* to their previous states.
	for s in f1
		dec!(s)
	end

	# Return the node with the maximum value in family as top and
	# the constructed sub-ZDDs as children.
	return getnode(top, child0, child1)
end

"""
Construct ZDD from family.
The family has to be represented as an *Iterable* of *Iterable*s of *Int*s.
"""
function tozdd(family)

	# Sort every set in *family* at first.
	# Because the max values of each set are repeatedly calculated,
	# it's more efficient to sort them at first.
	# Each set is reduced to its canonical sorted (descending) representation
	# with duplicate elements removed.
	function canonical_set(s)
		return sort!(unique(s), rev=true)
	end

	# *tozdd_sub!* assumes *family* does not contain duplication.
	# Deduplicate on the canonical *Vector{Int}* representation (which compares
	# by value) before wrapping them in *ArrayWithPos* (which does not).
	preprocessed_family = map(s -> ArrayWithPos(s, 1), unique(map(canonical_set, family)))
	root = tozdd_sub!(preprocessed_family)
	return ZDD(root)
end

"""
Returns true if zdd is an empty set. 
"""
isempty(zdd::ZDD) = isempty(zdd.root)

isempty(p::Node) = p === false_terminal

"""
Returns true if zdd is a base set.
"""
isbase(zdd::ZDD) = isbase(zdd.root)

isbase(p::Node) = p === true_terminal

# The unique (hash-cons) table keeps each node unique across the whole module.
# Keying by the *content* of the tuple (and comparing *Node*s by *==*, which is
# *===* for these mutable structs) gives correct identity-based sharing.
const _unique_table = Dict{Tuple{Int, Node, Node}, Node}()

# Operation caches (computed tables). Without them every recursive operation
# degrades to time proportional to the number of PATHS (i.e. the number of
# combinations, which is exponential) instead of the number of NODES.
# Plain *Dict* (NOT *IdDict*) is required: it hashes the tuple key by content
# and compares the contained *Node*s with *==* (which is *===* here), giving
# correct identity keying. *IdDict* would key by the freshly-allocated tuple's
# object identity and never hit.
const _union_cache     = Dict{Tuple{Node, Node}, Node}()
const _intersect_cache = Dict{Tuple{Node, Node}, Node}()
const _setdiff_cache   = Dict{Tuple{Node, Node}, Node}()
const _subset0_cache   = Dict{Tuple{Node, Int}, Node}()
const _subset1_cache   = Dict{Tuple{Node, Int}, Node}()
const _change_cache    = Dict{Tuple{Node, Int}, Node}()
const _length_cache    = Dict{Node, Int}()

"""
Generates node for given *top* value, *child0* and *child1* subgraph.
Using this method enables to keep each node unique.
"""
function getnode(top::Int, child0::Node, child1::Node)
	isempty(child1) && return child0
	return get!(() -> Node(top, child0, child1), _unique_table, (top, child0, child1))
end

function print_size()
	print(length(_unique_table))
	print("\n")
end

"""
Empty every internal cache (the unique/hash-cons table and all operation
caches), reclaiming the memory they hold.

WARNING: After calling this, do NOT operate on any ZDD that was built before
the clear. Clearing the unique table invalidates node identity/sharing, so
operations mixing pre- and post-clear nodes can produce incorrect results.
Only call *clear_caches!* between independent computations.
"""
function clear_caches!()
	empty!(_unique_table)
	empty!(_union_cache)
	empty!(_intersect_cache)
	empty!(_setdiff_cache)
	empty!(_subset0_cache)
	empty!(_subset1_cache)
	empty!(_change_cache)
	empty!(_length_cache)
	return nothing
end

"""

"""
function setdiff_sub(p::Node, q::Node)
	# Terminal / short-circuit cases are O(1); keep them before the cache.
	if isempty(p) | isempty(q)
		return p
	elseif p === q
		return false_terminal
	end
	return get!(_setdiff_cache, (p, q)) do
		if isbase(p)
			return setdiff_sub(p, q.child0)
		elseif isbase(q)
			return getnode(p.top, setdiff_sub(p.child0, q), p.child1)
		elseif p.top > q.top
			return getnode(p.top, setdiff_sub(p.child0, q), p.child1)
		elseif p.top < q.top
			return setdiff_sub(p, q.child0)
		else
			# p.top == q.top
			return getnode(
				p.top,
				setdiff_sub(p.child0, q.child0),
				setdiff_sub(p.child1, q.child1))
		end
	end
end

"""
Returns the set of combinations which are in *p* and not in *q*.
"""
function setdiff(p::ZDD, q::ZDD)
	return ZDD(setdiff_sub(p.root, q.root))
end

function subset1_sub(p::Node, v::Int)
	# A terminal node holds no combination containing *v*,
	# so the selected (and *v*-removed) family is empty.
	# These cases (and the comparisons against *v*) are O(1); keep them before
	# the cache and only memoize the recursive descent.
	if isempty(p) || isbase(p)
		return false_terminal
	elseif p.top < v
		return false_terminal
	elseif p.top == v
		return p.child1
	else # p.top > v
		return get!(_subset1_cache, (p, v)) do
			getnode(
				p.top,
				subset1_sub(p.child0, v),
				subset1_sub(p.child1, v))
		end
	end
end

"""
Select the set of combinations including *v* from *zdd*,
then delete *v* from them and return it.
"""
function subset1(zdd::ZDD, v::Int)
	return ZDD(subset1_sub(zdd.root, v))
end

function subset0_sub(p::Node, v::Int)
	# A terminal node holds no combination containing *v*,
	# so every combination it represents is kept unchanged.
	# These cases (and the comparisons against *v*) are O(1); keep them before
	# the cache and only memoize the recursive descent.
	if isempty(p) || isbase(p)
		return p
	elseif p.top < v
		return p
	elseif p.top == v
		return p.child0
	else # p.top > v
		return get!(_subset0_cache, (p, v)) do
			getnode(
				p.top,
				subset0_sub(p.child0, v),
				subset0_sub(p.child1, v))
		end
	end
end

"""
Select the combinations not including *v* from *zdd*.
"""
function subset0(zdd::ZDD, v::Int)
	return ZDD(subset0_sub(zdd.root, v))
end

function change_sub(p::Node, v::Int)
	# Toggling *v* over the empty family yields the empty family.
	# (The base terminal is handled by the *p.top < v* branch below, since
	#  *true_terminal.top == typemin(Int)*, turning {∅} into {{v}}.)
	# The empty and *p.top <= v* cases are O(1); only the recursive descent
	# (*p.top > v*) is memoized.
	if isempty(p)
		return p
	elseif p.top < v
		return getnode(v, false_terminal, p)
	elseif p.top == v
		return getnode(v, p.child1, p.child0)
	else # p.top > v
		return get!(_change_cache, (p, v)) do
			getnode(
				p.top,
				change_sub(p.child0, v),
				change_sub(p.child1, v))
		end
	end
end

"""
Inverts *v* on each combinations in *zdd*.
"""
function change(zdd::ZDD, v::Int)
	return ZDD(change_sub(zdd.root, v))
end

function union_sub(p::Node, q::Node)
	# Terminal / short-circuit cases are O(1); keep them before the cache.
	if isempty(p)
		return q
	elseif isempty(q)
		return p
	elseif p === q
		return p
	end
	return get!(_union_cache, (p, q)) do
		if isbase(q)
			return getnode(p.top, union_sub(p.child0, q), p.child1)
		elseif isbase(p)
			return getnode(q.top, union_sub(p, q.child0), q.child1)
		elseif p.top > q.top
			return getnode(p.top, union_sub(p.child0, q), p.child1)
		elseif p.top < q.top
			return getnode(q.top, union_sub(p, q.child0), q.child1)
		else
			return getnode(p.top, union_sub(p.child0, q.child0), union_sub(p.child1, q.child1))
		end
	end
end

"""
Returns the union set of *p* and *q*.
"""
function union(p::ZDD, q::ZDD)
	return ZDD(union_sub(p.root, q.root))
end

function intersect_sub(p::Node, q::Node)
	# Terminal / short-circuit cases are O(1); keep them before the cache.
	if isempty(p) | isempty(q)
		return false_terminal
	elseif p === q
		return p
	end
	return get!(_intersect_cache, (p, q)) do
		if p.top > q.top
			return intersect_sub(p.child0, q)
		elseif p.top < q.top
			return intersect_sub(p, q.child0)
		else # p.top == q.top
			return getnode(p.top, intersect_sub(p.child0, q.child0), intersect_sub(p.child1, q.child1))
		end
	end
end

"""
Returns the intersection set of *p* and *q*.
"""
function intersect(p::ZDD, q::ZDD)
	return ZDD(intersect_sub(p.root, q.root))
end

function length_sub(p::Node)
	# Terminal cases are O(1); keep them before the cache.
	if isempty(p)
		return 0
	elseif isbase(p)
		return 1
	else
		return get!(_length_cache, p) do
			length_sub(p.child0) + length_sub(p.child1)
		end
	end
end

"""
Returns the number of combinations in *zdd* as an *Int*.

Thanks to memoization the count runs in time proportional to the number of
NODES, not the number of combinations. Note that the result is an *Int* and may
overflow for families with more than 2^63 combinations.
"""
function length(zdd::ZDD)
	return length_sub(zdd.root)
end

end
