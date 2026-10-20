import Verified.Reflect.Command
import Examples.Words.Encode
import Examples.Trees.Encode

namespace Verified.Examples.RecursiveTypes

open Examples.Words Examples.Trees

def keepWords (xs : Words) : Words := xs

def duplicateWords (xs : Words) : Words × Words := (xs, xs)

def keepTree (tree : KeyTree) : KeyTree := tree

def duplicateTree (tree : KeyTree) : KeyTree × KeyTree := (tree, tree)

def emptyWords : Words := .nil

def prependWords (head : UInt64) (tail : Words) : Words := .cons head tail

def emptyTree : KeyTree := .leaf

def nodeTree (left : KeyTree) (key : UInt64) (right : KeyTree) : KeyTree := .node left key right

def reverseWords (xs acc : Words) : Words :=
  match xs with
  | .nil => acc
  | .cons head tail => reverseWords tail (.cons head acc)

def followRight (n : UInt64) (tree : KeyTree) : KeyTree :=
  if n = 0 then tree
  else match tree with
  | .leaf => .leaf
  | .node _ _ right => followRight (n - 1) right

verified_compile compiled := [keepWords, duplicateWords, keepTree, duplicateTree,
  emptyWords, prependWords, emptyTree, nodeTree, Words.first, KeyTree.setKey,
  KeyTree.leftChild, KeyTree.splitRoot, KeyTree.size, KeyTree.incr, Words.range,
  Words.sumAcc, reverseWords, followRight]

#print axioms compiled.keepWords.implements
#print axioms compiled.duplicateWords.implements
#print axioms compiled.keepTree.implements
#print axioms compiled.duplicateTree.implements

end Verified.Examples.RecursiveTypes
