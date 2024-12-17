import Aoc24

def main (args : List String) : IO Unit :=
  match args with
  | ["1"] => do
    IO.println "Day 1:"
    IO.println s!"Part 1: {← Day01.firstPart "input_01"}"
    IO.println s!"Part 2: {← Day01.secondPart "input_01"}"
    IO.println ""
  | ["2"] => do
    IO.println "Day 2:"
    IO.println s!"Part 1: {← Day02.firstPart "input_02"}"
    IO.println s!"Part 2: {← Day02.secondPart "input_02"}"
    IO.println ""
  | ["3"] => do
    IO.println "Day 3:"
    IO.println s!"Part 1: {← Day03.firstPart "input_03"}"
    IO.println s!"Part 2: {← Day03.secondPart "input_03"}"
    IO.println ""
  | ["4"] => do
    IO.println "Day 4:"
    IO.println s!"Part 1: {← Day04.firstPart "input_04"}"
    IO.println s!"Part 2: {← Day04.secondPart "input_04"}"
    IO.println ""
  | ["5"] => do
    IO.println "Day 5:"
    IO.println s!"Part 1: {← Day05.firstPart "input_05"}"
    IO.println s!"Part 2: {← Day05.secondPart "input_05"}"
    IO.println ""
  | ["6"] => do
    IO.println "Day 6:"
    IO.println s!"Part 1: {← Day06.firstPart "input_06"}"
    IO.println s!"Part 2: {← Day06.secondPart "input_06"}"
    IO.println ""
  | ["7"] => do
    IO.println "Day 7:"
    IO.println s!"Part 1: {← Day07.firstPart "input_07"}"
    IO.println s!"Part 2: {← Day07.secondPart "input_07"}"
    IO.println ""
  | ["8"] => do
    IO.println "Day 8:"
    IO.println s!"Part 1: {← Day08.firstPart "input_08"}"
    IO.println s!"Part 2: {← Day08.secondPart "input_08"}"
    IO.println ""
  | ["9"] => do
    IO.println "Day 9:"
    IO.println s!"Part 1: {← Day09.firstPart "input_09"}"
    IO.println s!"Part 2: {← Day09.secondPart "input_09"}"
    IO.println ""
  | ["10"] => do
    IO.println "Day 10:"
    IO.println s!"Part 1: {← Day10.firstPart "input_10"}"
    IO.println s!"Part 2: {← Day10.secondPart "input_10"}"
    IO.println ""
  | ["11"] => do
    IO.println "Day 11:"
    IO.println s!"Part 1: {← Day11.firstPart "input_11" 25}"
    IO.println s!"Part 2: {← Day11.secondPart "input_11" 75}"
    IO.println ""
  | ["11t", s] => do
    IO.println "Day 11:"
    IO.println s!"Part 1: {← Day11.firstPart "input_11_test3" s.toNat!}"
    IO.println s!"Part 2: {← Day11.secondPart "input_11_test3" s.toNat!}"
    IO.println ""
  | ["12"] => do
    IO.println "Day 12:"
    IO.println s!"Part 1: {← Day12.firstPart "input_12"}"
    IO.println s!"Part 2: {← Day12.secondPart "input_12"}"
    IO.println ""
  | ["12", s] => do
    IO.println "Day 12:"
    IO.println s!"Part 1: {← Day12.firstPart s}"
    IO.println s!"Part 2: {← Day12.secondPart s}"
    IO.println ""
  | ["13"] => do
    IO.println "Day 13:"
    IO.println s!"Part 1: {← Day13.firstPart "input_13"}"
    IO.println s!"Part 2: {← Day13.secondPart "input_13"}"
    IO.println ""
  | ["14"] => do
    IO.println "Day 14:"
    IO.println s!"Part 1: {← Day14.firstPart "input_14" 101 103}"
    IO.println s!"Part 2: {← Day14.secondPart "input_14"}"
    IO.println ""
  | ["15"] => do
    IO.println "Day 15:"
    IO.println s!"Part 1: {← Day15.firstPart "input_15"}"
    IO.println s!"Part 2: {← Day15.secondPart "input_15"}"
    IO.println ""
  | ["16"] => do
    IO.println "Day 16:"
    IO.println s!"Part 1: {← Day16.firstPart "input_16"}"
    IO.println s!"Part 2: {← Day16.secondPart "input_16"}"
    IO.println ""
  | ["17"] => do
    IO.println "Day 17:"
    IO.println s!"Part 1: {← Day17.firstPart "input_17"}"
    IO.println s!"Part 2: {← Day17.secondPart "input_17"}"
    IO.println ""
  | ["17t"] => do
    IO.println "Day 17:"
    --IO.println s!"Part 1: {← Day17.firstPart "input_17_test1"}"
    IO.println s!"Part 2: {← Day17.secondPart "input_17_test1"}"
    IO.println ""
  | _ => do
    IO.println "Help, what should I do!?"
