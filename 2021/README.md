# Meetings 2021

## E01: February

Social meeting.

## E02: March

Social meeting.

## E03: April

Social meeting.

## E04: May

* Jack Kelly: **_Haskell and Lambda at Bellroy (wai-handler-hal)_**

  In this talk, I'll discuss how Bellroy uses the hal library to build Haskell binaries that run on AWS Lambda. From there, I'll introduce our new library, wai-handler-hal, which makes it easy to host WAI applications on Lambda behind an AWS API Gateway. I'll also discuss deployment and security considerations, and some surprising payoffs we get from well-designed abstractions lower down in the stack.

* Amos Robinson: **_Verifying safety-critical C code with Frama-C_**

  Pure functional programming is great for writing programs that are easy to reason about. Unfortunately, it's not always great at running those programs in restricted environments. What do we do when we need to reason about programs, but can't afford the runtime overhead of a garbage collector or memory allocator, and we don't want to alienate the systems engineers? One option is to write a pure (but not necessarily functional) specification and prove that the C implementation refines it. This is the premise of Frama-C.

  In this talk I'll show off some of the fun I've been having verifying safety-critical C code with Frama-C, and why I think it's more practical than other automated theorem provers.

## E05: June

* Barry Jay: **_An Equational Account of Variables and Abstractions_**

  VA-calculus supports abstractions as combinations of two operators, for variables and abstractions, evaluated by simple equations. This avoids the complexity of the beta-rule of lambda-calculus while still supporting combinators and the usual arithmetic functions. Further, abstractions can now be tagged in a way that does not interfere with their functional behaviour. Tags may include type information, so that each typed calculus becomes a sub-system of the original. Nevertheless, VA-calculus is not as expressive as tree calculus, as it cannot decide equality of programs.

## E06: July

* Huw Campbell: **_Recursive Data Structures in Columnar and Wire Data Formats_**

  Recursive types, along with sum types and product types, can be efficiently encoded in packed columnar binary file formats, as well as the record based binary data formats which have been previously described.
  One can thus provide excellent storage and performance characteristics both over the wire and in bulk storage. In this talk I'll present a new schema specification type, which fixes many of the limitations of commonly used formats; and talk about their on disk representation and how to upgrade and migrate schemas.


## E07: August

No meeting (clash with ICFP 2021, online edition).

## E08: September

* Mark Hopkins: **_Playing with Patterns_** ([slides](./2021-09-22-HopkinsM-and-and-or-patterns.pdf))

  We'll take a look at a work-in-progress grammar model for Turkish (an agglutinative language with vowel harmony) and see how some tricks with patterns in Haskell can help us write cleaner code.

  Links mentioned in the talk:

  * [Arnold de Vos: Querying a dataset with Scala's pattern matching](https://notes.backgroundsignal.com/Querying_a_Dataset_with_Scala_s_Pattern_Matching.html)
  * https://hackage.haskell.org/package/OrPatterns
  * https://github.com/ghc-proposals/ghc-proposals/pull/43

* Mark Hopkins: **_Golden round-trip testing_**

  Golden tests and round-trip testing are both useful techniques that deserve to be in every programmer's tool belt, but it turns out a mashup of the two is even better.

## E09: October
* Darren Ldl: **_Timere: an OCaml time handling library_**

  Time handling is commonly considered a difficult problem by programmers due to myriad standards and complexity of time zone definitions. This also complicates scheduling across multiple time zones especially when one takes Daylight Saving Time into account. We present a highly expressive set of APIs, Timere, which can describe scheduling requirements precisely with flexible time zone handling, along with a natural language parser that can handle common English phrases. We also contribute a new date time handling library as part of the work.
* Tim McGilchrist - **_Building an OCaml CI System_**

## E10: November
Cancelled.