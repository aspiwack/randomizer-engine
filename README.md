Randomizer Engine
=================

We're Randomizer Engine, but we're thinking of changing the name

### Credits

Almost all the good ideas which went and are going to go into this
project are Simon Cruanes's (@c-cube).

## What is it?

Randomisers are a recent popular trend in video game. The modern trend
and form has been started by [Zelda: A Link to the Past
Randomizer][alttpr].

The principle is the following: a game has a number of items to find
in order to complete the game. These items are shuffled around before
the game start, and the player must now find a good way to game
completion.

Randomisers have a logic in place to make sure that the shuffles are
always completable (_e.g._ in _a link to the past_, the bow cannot be
in a location which requires the bow to reach (such as the Palace of
Darkness boss reward)). Generating a logical shuffle is done in an _ad
hoc_ way in existing randomisers. As a result, there is no guarantee
that the various shuffles are fairly distributed across random
runs. Furthermore changing the logic, or adapting it for variants, is
hard (at least it requires serious thoughts) and error prone.

Randomizer Engine is a _generic_ tool which produces _uniformly_
random shuffles for a _declarative_ logic. I don't know, at this point
whether this has more than academic value (it may very well be that
uniformly random shuffles are, in fact, not fun to play. Or that this
project never scales to meet the demand of a real life randomiser).

## The game plan

Randomizer Engine is far from done. But here is more or less what it
will look like.

Randomizer Engine will be an executable program which takes, as an
input, a logic, and produces a method to produce random shuffle.

### Logic

The logic will consist in the declaration of

- a bunch of locations
- a pool of items (there will be the possibility to have more than one
  of an item)
- location restrictions (_ranges_) for items, such as `"Palace of Darkness Key"
  in {"Palace of Darkness: chest 1", "Palace of Darkness: chest 2",
  …}`
- a logic program on predicates `reach: <location>` and `have:
  <item>`, with clauses such as `have: Book, have: Boots -> reach:
  "Desert Palace: torch"`
  
### The output

The output will be, basically, a flow chart of weighted binary
decision (left or right?): for each binary decision, the chart tells you that there are
`n` possible shuffle for left, and `k` for right. Pick a random
integer between `0` and `n+k-1`, if it's strictly smaller than `n`, go
left, otherwise go right.

The number of decisions will be `O(item*location)`.

Technically, the flow chart will be a [Zero-supressed Decision
Diagram][zdd-wiki] (or, rather, a path counting variant of it).

### Handling different logics

Randomisers typically have options which modify the logic. For
instance, _a link to the past randomizer_ has three different
“states”: standard, open, and inverted.

These logics have a lot in common, therefore we want to share them at
two levels: the input should share stanzas, and the output should
represent all the logic (it's better compression and, more
importantly, it prevents having to generate an output file for each
combination of options).

To that effect, options are represented as variables. In the output,
it suffices to follow the left or right path depending on whether the
option is set. In the input they would appear on the left-hand side of
rules:

```
"State: standard", have: "Titan's mitts", have: Flippers, have: "Ice rod" -> reach: "Ice Palace: chest 1"
"State: inverted", have: Flippers, have: "Ice rod" -> reach: "Ice Palace: chest 1"
```

I don't have a good solution, yet, to handle changing the items in the
pool (such as the fact that, in _a link to the past randomizer_, there are
more occurrences of the sword in “easy” mode, as well as an extra
“Quarter magic” item)

[alttpr]: https://alttpr.com/
[zdd-wiki]: https://en.wikipedia.org/wiki/Zero-suppressed_decision_diagram
