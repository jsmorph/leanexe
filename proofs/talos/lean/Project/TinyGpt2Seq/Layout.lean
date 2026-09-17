namespace Project.TinyGpt2Seq.Layout

def context : Nat := 128
def token : Nat := 0
def position : Nat := 1024
def query : Nat := 1536
def key : Nat := 1552
def value : Nat := 1568
def attention : Nat := 1584
def attentionBias : Nat := 1600
def expand : Nat := 1604
def expandBias : Nat := 1636
def contract : Nat := 1644
def contractBias : Nat := 1676
def head : Nat := 1680
def headBias : Nat := 2704
def norm1 : Nat := 2960
def norm2 : Nat := 2968
def normFinal : Nat := 2976
def size : Nat := 2984

end Project.TinyGpt2Seq.Layout
