namespace LeanExe
namespace Runtime

def allocCount : UInt64 :=
  0

def retainCount : UInt64 :=
  0

def releaseCount : UInt64 :=
  0

def freeCount : UInt64 :=
  0

def release {α : Type} (_value : α) : UInt64 :=
  0

end Runtime
end LeanExe
