# monoidal-rows

This is an experimental type system based on various works, most notably
[Abstracting Extensible Data Types or Rows By Any Other Name](https://dl.acm.org/doi/10.1145/3290325)

The initial row implementation was a fairly exact replica of the row theory
termed "simple rows" in that paper. I have since extended it with a number of
features of varying ambition and theoretical soundness.

- [Features](#features)
    + [Monoidal rows](#monoidal-rows)
    + [Pattern matching inference](#pattern-matching-inference)
    + [Effect rows](#effect-rows)
    + [Data constraints](#data-constraints)
    + [Layout polymorphism](#layout-polymorphism)
- [Usage](#usage)
- [Discussion](#discussion)

## Features

### Monoidal rows
The basic concept here is the inclusion of the row concatenation constraint
`ζ₁ ⊙ ζ₂ ~ ζ₃` which is the only way to combine rows in this system, and stands
in contrast to other systems where in the usual method of row combination is via
extension.

Ie, rather than type constructors
```hs
data Type
    = ...
    | TRowExtend Field Type
    | TRowNil
```
You have only a type constructor like
```hs
data Type
    = ...
    | TRow (Map Name Type)
```
and combination is done via constraint solving

Additionally, there is a constraint for row subtyping `ζ₁ ◁ ζ₂`, which allows
constraining a row to a subset of another. This is representable in terms of the
concatenation constraint, and in other implementations based on this paper it
is; however I have found it allows a nice syntactic simplification of many
constraints and so I have chosen to leave it as its own constraint constructor.

Despite the `⊙` operation being associative and commutative, the rows are
technically still only partial monoids, as the union produced is expected to be
disjoint.

### Pattern matching inference
The first extension made to the implementation in comparison to that of the
original paper was to replace the branch operation `Δ` with a pattern matching
implementation. This is a very straight-forward addition, and the features I
have gone with here could easily be extended further; for example I have product
row patterns as always producing a sub-row constraint, but other types of
patterns would easily extend this, such as making the current system accessible
via an additive ".." pattern, and expecting patterns without this qualifier to
emit an exact constraint.

This just required extending the AST with a Patt type and mirroring the infer
and check functions as inferPatt and checkPatt

### Effect rows
The most theoretically sketchy addition I have made here is to distinguish
between the existing rows (re-termed data row) and effects rows, with the effect
rows being simple lists of types rather than maps. The sketchy part being that I
allow instantiation of effect constructors at multiple different parameters in
the same row. This leads to a rather complicated constraint
reduction/unification strategy, and the consequences of my implementation have
not been fully explored.

Notably, because effect constructors can be instantiated at multiple types, we
cannot always unify variables immediately. I have chosen to unify where there is
only one option and to emit a sub-row constraint where there are multiple. One
can imagine this may lead to unsoundness in some scenario, though my testing has
not revealed any such problems yet. A simple fix for this, if it proves to be
problematic, would simply be to not unify the free meta-variables inside effect
rows at all, and to expect other uses of the variable to provide the unification
for us.

Various things were added to the implementation to support the effect rows,
including a handler term, evidence passing during inference, and an extension to
the environment containing effect definitions.

### Data constraints
This simple extension adds a new member to the environment containing data type
-> row associations, and two new constraints allowing the binding of a type to
be a data type of either product or row construction. TProd and TSum type
constructors become ephemeral constraint-passing markers for use with check, and
instead of inferring all uses of rows as instantiations of TProd or TRow we
instead infer them to be instantiations of variable type constrained to an
appropriate row association.

The inclusion of this feature is designed to counter the usual problems of
structural typing; ie incompatibility with systems like typeclasses, and the
need for complex methods to work with recursive aliases. This allows us to have
our row polymorphism, with the same level of expressivity, while maintaining
nominative type system features as well. This has no impact on theoretic
soundness, but does lead to more verbose signatures. This could be combatted by
the addition of inline constraints like those used in the original paper, which
would presumably be lifted into the current qualifier system at kind inference.

### Layout polymorphism
This is another large addition, but turned out not to have nearly the same
sketchy theoretical implications as the effect rows, though the method of solve
is quite similar.

Essentially, I borrow and extend concepts from implementations of first-class
labels (a la [First Class Labels for Extensible Rows](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/fclabels.pdf))
in order to allow a new kind of polymorphic variance over data. In data rows,
instead of a map from strings to types, we now have an associative array of
labels to types, where labels are themselves a pair of types. The types
contained in this pair are expected to always be of the kinds Int and String
respectively; in other words we lift integers and strings to the type level to
serve together as our label. The string obviously serves the same purpose as before,
while the addition of the integer allows us to talk about the layout of our data.

Unlike in systems with true first-class labels, I do not allow full polymorphic
variance over the entire label of a given field. Instead, either the layout or
the name must always be specified. This limitation simplifies the constraint
solving to a great degree and allows it to be easily shown as sound, avoiding
the problem encountered in effects rows. Multiple possible unifications of
labels are invariably an error.

To support this feature I added new forms to the AST in terms and pattern
matching, that each allow either variance over layout or naming of their
specified structures. This is fairly straight forward, and just leads to a bit
of code repetition as we decide between creation of fresh meta variables for
either the layout or name in labels. As it is quite verbose, I have left the
syntax extension quite simple, but a much more expressive syntax should only
require an equally straight forward modification; one could imagine for example
allowing variance over some fields but not others with optional syntax.

The idea with this feature was to circumvent another typical problem with row
types, that being that layout is generally chosen by the compiler, making it
somewhat incompatible with usage in systems-level languages. The concept here is
that, when defining a data type, the layout is always that given by the
programmer, and when utilizing the data type at term (and pattern) level, the
layout can be ignored. The simple addition of allowing the programmer to talk
about the layout at term level also leads to syntactic conveniences, such as (in
the case of un-curried functions using tuples for their n-ary argument passing)
allowing a simple implementation of positional and named argument syntax. It
also allows dual-construction syntax like that of Haskell data types. I also
extended the usage of rows this way for sums, which at a term/pattern level may
have limited use; however, being able to define the discriminator in data type
definitions is obviously of some utility, if a language gives access to the
underlying structure of sums.

## Usage
There is no parser or driver here. The expected usage is as a reference, but if
you would like to play with the inference there is a convenient `test` function
in Main for use in GHCi.

The code here is licensed under MIT, do whatever you like with it. I'd like to
hear from you if it turns out to be useful to you in a project or
self-education.

For my own future and expanded work based on this study,
check out the [Ribbon](https://ribbon-lang.github.io) programming language.
It is an embeddable algebraic effects language with a focus on
data polymorphism and structured allocation, motivated by deep extensibility
in the style of Lua/LISP.

## Discussion
Contact me:
+ by email at noxabellus@gmail.com
+ on Discord, my username there is `noxabellus`;
I can be found on various dev servers
([fp](https://discord.com/invite/FvT2Y5N),
[r/pl](https://discord.com/invite/tuFCPmB7Un), etc)
and DMs are open as well

I would love to hear any thoughts you have relating to
soundness or potential additions

PRs without prior discussion are discouraged
