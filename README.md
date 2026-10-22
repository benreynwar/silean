# Silean

This repository contains 2 projects, Silean1 and Silean2.

## Silean1

This project is a heavily AI-assisted experiment to see if a
proof-assistant-centric approach to hardware RTL design is practical yet. The
conclusion was that it is now practical.  I've ported a high throughput FFT design
that I wrote in VHDL 5 years ago
[github.com/benreynwar/htfft](github.com/benreynwar/htfft) to a version
embedded in lean and proved it's equivalence within a specified error bound to
the Mathlib complex DFT.
For more details see [`Silean1/README.md`](Silean1/README.md).

## Silean2

This is a second version of the project using much less AI assistance.  The goal
is for it to be a better designed version of Silean1.

LLM Usage Scale
 0 - A project I wrote myself
 2
 4 <--------- Silean2
 6
 8 <--------- Silean1
10 - A project entirely written by an LLM
