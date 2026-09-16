namespace Project.TinyGpt2.Layout

def token : Nat := 0
def position : Nat := 1024
def query : Nat := 1040
def key : Nat := 1056
def value : Nat := 1072
def attention : Nat := 1088
def attentionBias : Nat := 1104
def expand : Nat := 1108
def expandBias : Nat := 1140
def contract : Nat := 1148
def contractBias : Nat := 1180
def head : Nat := 1184
def headBias : Nat := 2208
def norm1 : Nat := 2464
def norm2 : Nat := 2472
def normFinal : Nat := 2480
def size : Nat := 2488

end Project.TinyGpt2.Layout
