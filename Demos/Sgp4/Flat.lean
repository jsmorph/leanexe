import Demos.Sgp4.Program
import LeanExe.Pipeline.Implements

namespace Demos.Sgp4

open LeanExe.Pipeline

instance : Flat Consts (UInt64 × UInt64 × Float × Float × Float × Float × Float × Float × Float ×
    Float × Float × Float × Float × Float × Float × Float × Float × Float × Float × Float ×
    Float × Float × Float × Float × Float × Float × Float × Float × Float × Float × Float ×
    Float × Float × Float × Float) :=
  ⟨fun c => (c.status, c.isimp, c.no, c.ecco, c.inclo, c.nodeo, c.argpo, c.mo, c.bstar, c.sinio,
    c.cosio, c.con41, c.x1mth2, c.x7thm1, c.mdot, c.argpdot, c.nodedot, c.nodecf, c.cc1, c.cc4,
    c.cc5, c.t2cof, c.omgcof, c.eta, c.xmcof, c.delmo, c.sinmao, c.d2, c.d3, c.d4, c.t3cof,
    c.t4cof, c.t5cof, c.aycof, c.xlcof)⟩

instance : Flat State (UInt64 × Float × Float × Float × Float × Float × Float) :=
  ⟨fun s => (s.status, s.x, s.y, s.z, s.vx, s.vy, s.vz)⟩

end Demos.Sgp4
