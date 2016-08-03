# Agda exercises

## Division

A natural number `m` divides another natural number `n` if there exists some
natural number `k` such that `n = k * m`.

  1. Define a predicate `_divides_` that asserts that one natural number divides
     another.

  2. Show that the predicate above is decidable.

  3. Show that all natural numbers are divisible by themselves and by 1.

  4. Try to write a function `divide` that takes two natural numbers and
     computes the natural number division of the first argument by the second
     using repeated subtraction.  What problem do you encounter?

## Fizzbuzz

Using your `_divides_` predicate above, and using any other definitions in the
Agda standard library to help that are not directly connected with division,
complete the following:

  1. The fizzbuzz drinking game consists of players taking it in turns to count
     consecutively upwards, starting from zero.  Some numbers, however, are
     special: on numbers that are divisible by 3, players miss the number and
     instead say "Fizz", on numbers divisible by 5 they miss the number and
     instead say "Buzz", and on numbers divisible by both 3 and 5 they miss the
     number and instead say "Fizzbuzz".  A player saying the wrong thing must
     drink some of his or her drink, and then the game restarts.

     For a given natural number `n`, create a declarative specification, modelled
     as an Agda datatype, of the expected word that a player correctly playing
     the fizzbuzz game should say on their turn, given the group has collectively
     counted up to `n`.

  2. Write an Agda function that, given a natural number `n`, returns the
     correct word that a player correctly playing the fizzbuzz game should say
     on their turn, given the group has collectively counted up to `n`.

  3. Show that your function defined in part (2) above is sound for the
     declarative specification defined in part (1) above, in the sense that if
     at a given turn `n` the function computes the string `ss`, then the
     declarative relation also agrees.

  4. Show that your function defined in part (2) above is complete for the
     declarative specification defined in part (1) above, in the sense that if
     at a given turn `n` the declarative specification states that the string
     `ss` is associated with turn `n` then the function computes `ss` at `n`.

  5. Using the function defined above, use the definitions in `Data.Stream` or
     otherwise to compute an infinite stream of expected responses from a group
     of people correctly playing the fizzbuzz game in perpetuity.
