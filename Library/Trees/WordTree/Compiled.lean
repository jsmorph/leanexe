module

public import Library.Trees.WordTree.Program
public import Verified.Reflect.Command
public import Library.Trees.WordTree.Reflected

@[expose] public section

namespace Library.Trees.WordTree

verified_compile compiled := [KeyTree.size, KeyTree.sum, KeyTree.height, KeyTree.incr, KeyTree.setKey, KeyTree.insert, KeyTree.leftChild, KeyTree.splitRoot]

end Library.Trees.WordTree
