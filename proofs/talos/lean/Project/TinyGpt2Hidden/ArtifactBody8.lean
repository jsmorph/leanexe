import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

@[cbv_eval] theorem sequence8_13_e_5_t_tail1 :
    instructionSequenceAt 718 true { bytes := artifactBytes, pos := 1478, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[13]!) true)[5]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 1479, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_13_e_5_t_tail0 :
    instructionSequenceAt 719 true { bytes := artifactBytes, pos := 1477, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[13]!) true)[5]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 1479, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_13_e_5_e_tail3 :
    instructionSequenceAt 716 false { bytes := artifactBytes, pos := 1484, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[13]!) true)[5]!) true).drop 3, .end), { bytes := artifactBytes, pos := 1485, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_13_e_5_e_tail0 :
    instructionSequenceAt 719 false { bytes := artifactBytes, pos := 1479, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[13]!) true)[5]!) true).drop 0, .end), { bytes := artifactBytes, pos := 1485, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_46_e_5_t_tail1 :
    instructionSequenceAt 685 true { bytes := artifactBytes, pos := 1568, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[46]!) true)[5]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 1569, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_46_e_5_t_tail0 :
    instructionSequenceAt 686 true { bytes := artifactBytes, pos := 1567, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[46]!) true)[5]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 1569, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_46_e_5_e_tail3 :
    instructionSequenceAt 683 false { bytes := artifactBytes, pos := 1574, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[46]!) true)[5]!) true).drop 3, .end), { bytes := artifactBytes, pos := 1575, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_46_e_5_e_tail0 :
    instructionSequenceAt 686 false { bytes := artifactBytes, pos := 1569, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[46]!) true)[5]!) true).drop 0, .end), { bytes := artifactBytes, pos := 1575, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_82_e_5_t_tail1 :
    instructionSequenceAt 649 true { bytes := artifactBytes, pos := 1661, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[82]!) true)[5]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 1662, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_82_e_5_t_tail0 :
    instructionSequenceAt 650 true { bytes := artifactBytes, pos := 1660, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[82]!) true)[5]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 1662, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_82_e_5_e_tail3 :
    instructionSequenceAt 647 false { bytes := artifactBytes, pos := 1667, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[82]!) true)[5]!) true).drop 3, .end), { bytes := artifactBytes, pos := 1668, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_82_e_5_e_tail0 :
    instructionSequenceAt 650 false { bytes := artifactBytes, pos := 1662, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[82]!) true)[5]!) true).drop 0, .end), { bytes := artifactBytes, pos := 1668, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_115_e_5_t_tail1 :
    instructionSequenceAt 616 true { bytes := artifactBytes, pos := 1751, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[115]!) true)[5]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 1752, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_115_e_5_t_tail0 :
    instructionSequenceAt 617 true { bytes := artifactBytes, pos := 1750, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[115]!) true)[5]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 1752, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_115_e_5_e_tail3 :
    instructionSequenceAt 614 false { bytes := artifactBytes, pos := 1757, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[115]!) true)[5]!) true).drop 3, .end), { bytes := artifactBytes, pos := 1758, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_115_e_5_e_tail0 :
    instructionSequenceAt 617 false { bytes := artifactBytes, pos := 1752, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[115]!) true)[5]!) true).drop 0, .end), { bytes := artifactBytes, pos := 1758, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_151_e_5_t_tail1 :
    instructionSequenceAt 580 true { bytes := artifactBytes, pos := 1844, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[151]!) true)[5]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 1845, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_151_e_5_t_tail0 :
    instructionSequenceAt 581 true { bytes := artifactBytes, pos := 1843, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[151]!) true)[5]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 1845, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_151_e_5_e_tail3 :
    instructionSequenceAt 578 false { bytes := artifactBytes, pos := 1850, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[151]!) true)[5]!) true).drop 3, .end), { bytes := artifactBytes, pos := 1851, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_151_e_5_e_tail0 :
    instructionSequenceAt 581 false { bytes := artifactBytes, pos := 1845, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[151]!) true)[5]!) true).drop 0, .end), { bytes := artifactBytes, pos := 1851, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_184_e_5_t_tail1 :
    instructionSequenceAt 547 true { bytes := artifactBytes, pos := 1934, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[184]!) true)[5]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 1935, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_184_e_5_t_tail0 :
    instructionSequenceAt 548 true { bytes := artifactBytes, pos := 1933, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[184]!) true)[5]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 1935, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_184_e_5_e_tail3 :
    instructionSequenceAt 545 false { bytes := artifactBytes, pos := 1940, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[184]!) true)[5]!) true).drop 3, .end), { bytes := artifactBytes, pos := 1941, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_184_e_5_e_tail0 :
    instructionSequenceAt 548 false { bytes := artifactBytes, pos := 1935, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[184]!) true)[5]!) true).drop 0, .end), { bytes := artifactBytes, pos := 1941, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_220_e_5_t_tail1 :
    instructionSequenceAt 511 true { bytes := artifactBytes, pos := 2027, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[220]!) true)[5]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 2028, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_220_e_5_t_tail0 :
    instructionSequenceAt 512 true { bytes := artifactBytes, pos := 2026, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[220]!) true)[5]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 2028, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_220_e_5_e_tail3 :
    instructionSequenceAt 509 false { bytes := artifactBytes, pos := 2033, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[220]!) true)[5]!) true).drop 3, .end), { bytes := artifactBytes, pos := 2034, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_220_e_5_e_tail0 :
    instructionSequenceAt 512 false { bytes := artifactBytes, pos := 2028, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[220]!) true)[5]!) true).drop 0, .end), { bytes := artifactBytes, pos := 2034, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_253_e_5_t_tail1 :
    instructionSequenceAt 478 true { bytes := artifactBytes, pos := 2117, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[253]!) true)[5]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 2118, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_253_e_5_t_tail0 :
    instructionSequenceAt 479 true { bytes := artifactBytes, pos := 2116, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[253]!) true)[5]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 2118, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_253_e_5_e_tail3 :
    instructionSequenceAt 476 false { bytes := artifactBytes, pos := 2123, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[253]!) true)[5]!) true).drop 3, .end), { bytes := artifactBytes, pos := 2124, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_253_e_5_e_tail0 :
    instructionSequenceAt 479 false { bytes := artifactBytes, pos := 2118, limit := 2178 } =
      .ok (((Instr.childBody ((Instr.childBody ((Cache.raw.codes[8]!.body)[253]!) true)[5]!) true).drop 0, .end), { bytes := artifactBytes, pos := 2124, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_13_t_tail1 :
    instructionSequenceAt 725 true { bytes := artifactBytes, pos := 1466, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[13]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 1467, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_13_t_tail0 :
    instructionSequenceAt 726 true { bytes := artifactBytes, pos := 1464, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[13]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 1467, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_13_e_tail6 :
    instructionSequenceAt 720 false { bytes := artifactBytes, pos := 1485, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[13]!) true).drop 6, .end), { bytes := artifactBytes, pos := 1486, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_13_e_tail0 :
    instructionSequenceAt 726 false { bytes := artifactBytes, pos := 1467, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[13]!) true).drop 0, .end), { bytes := artifactBytes, pos := 1486, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_21_t_tail1 :
    instructionSequenceAt 717 true { bytes := artifactBytes, pos := 1501, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[21]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 1502, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_21_t_tail0 :
    instructionSequenceAt 718 true { bytes := artifactBytes, pos := 1500, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[21]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 1502, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_21_e_tail1 :
    instructionSequenceAt 717 false { bytes := artifactBytes, pos := 1504, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[21]!) true).drop 1, .end), { bytes := artifactBytes, pos := 1505, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_21_e_tail0 :
    instructionSequenceAt 718 false { bytes := artifactBytes, pos := 1502, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[21]!) true).drop 0, .end), { bytes := artifactBytes, pos := 1505, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_46_t_tail1 :
    instructionSequenceAt 692 true { bytes := artifactBytes, pos := 1556, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[46]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 1557, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_46_t_tail0 :
    instructionSequenceAt 693 true { bytes := artifactBytes, pos := 1554, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[46]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 1557, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_46_e_tail6 :
    instructionSequenceAt 687 false { bytes := artifactBytes, pos := 1575, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[46]!) true).drop 6, .end), { bytes := artifactBytes, pos := 1576, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_46_e_tail0 :
    instructionSequenceAt 693 false { bytes := artifactBytes, pos := 1557, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[46]!) true).drop 0, .end), { bytes := artifactBytes, pos := 1576, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_54_t_tail1 :
    instructionSequenceAt 684 true { bytes := artifactBytes, pos := 1591, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[54]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 1592, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_54_t_tail0 :
    instructionSequenceAt 685 true { bytes := artifactBytes, pos := 1590, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[54]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 1592, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_54_e_tail1 :
    instructionSequenceAt 684 false { bytes := artifactBytes, pos := 1594, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[54]!) true).drop 1, .end), { bytes := artifactBytes, pos := 1595, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_54_e_tail0 :
    instructionSequenceAt 685 false { bytes := artifactBytes, pos := 1592, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[54]!) true).drop 0, .end), { bytes := artifactBytes, pos := 1595, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_82_t_tail1 :
    instructionSequenceAt 656 true { bytes := artifactBytes, pos := 1649, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[82]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 1650, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_82_t_tail0 :
    instructionSequenceAt 657 true { bytes := artifactBytes, pos := 1647, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[82]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 1650, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_82_e_tail6 :
    instructionSequenceAt 651 false { bytes := artifactBytes, pos := 1668, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[82]!) true).drop 6, .end), { bytes := artifactBytes, pos := 1669, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_82_e_tail0 :
    instructionSequenceAt 657 false { bytes := artifactBytes, pos := 1650, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[82]!) true).drop 0, .end), { bytes := artifactBytes, pos := 1669, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_90_t_tail1 :
    instructionSequenceAt 648 true { bytes := artifactBytes, pos := 1684, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[90]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 1685, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_90_t_tail0 :
    instructionSequenceAt 649 true { bytes := artifactBytes, pos := 1683, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[90]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 1685, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_90_e_tail1 :
    instructionSequenceAt 648 false { bytes := artifactBytes, pos := 1687, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[90]!) true).drop 1, .end), { bytes := artifactBytes, pos := 1688, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_90_e_tail0 :
    instructionSequenceAt 649 false { bytes := artifactBytes, pos := 1685, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[90]!) true).drop 0, .end), { bytes := artifactBytes, pos := 1688, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_115_t_tail1 :
    instructionSequenceAt 623 true { bytes := artifactBytes, pos := 1739, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[115]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 1740, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_115_t_tail0 :
    instructionSequenceAt 624 true { bytes := artifactBytes, pos := 1737, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[115]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 1740, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_115_e_tail6 :
    instructionSequenceAt 618 false { bytes := artifactBytes, pos := 1758, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[115]!) true).drop 6, .end), { bytes := artifactBytes, pos := 1759, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_115_e_tail0 :
    instructionSequenceAt 624 false { bytes := artifactBytes, pos := 1740, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[115]!) true).drop 0, .end), { bytes := artifactBytes, pos := 1759, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_123_t_tail1 :
    instructionSequenceAt 615 true { bytes := artifactBytes, pos := 1774, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[123]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 1775, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_123_t_tail0 :
    instructionSequenceAt 616 true { bytes := artifactBytes, pos := 1773, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[123]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 1775, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_123_e_tail1 :
    instructionSequenceAt 615 false { bytes := artifactBytes, pos := 1777, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[123]!) true).drop 1, .end), { bytes := artifactBytes, pos := 1778, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_123_e_tail0 :
    instructionSequenceAt 616 false { bytes := artifactBytes, pos := 1775, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[123]!) true).drop 0, .end), { bytes := artifactBytes, pos := 1778, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_151_t_tail1 :
    instructionSequenceAt 587 true { bytes := artifactBytes, pos := 1832, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[151]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 1833, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_151_t_tail0 :
    instructionSequenceAt 588 true { bytes := artifactBytes, pos := 1830, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[151]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 1833, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_151_e_tail6 :
    instructionSequenceAt 582 false { bytes := artifactBytes, pos := 1851, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[151]!) true).drop 6, .end), { bytes := artifactBytes, pos := 1852, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_151_e_tail0 :
    instructionSequenceAt 588 false { bytes := artifactBytes, pos := 1833, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[151]!) true).drop 0, .end), { bytes := artifactBytes, pos := 1852, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_159_t_tail1 :
    instructionSequenceAt 579 true { bytes := artifactBytes, pos := 1867, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[159]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 1868, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_159_t_tail0 :
    instructionSequenceAt 580 true { bytes := artifactBytes, pos := 1866, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[159]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 1868, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_159_e_tail1 :
    instructionSequenceAt 579 false { bytes := artifactBytes, pos := 1870, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[159]!) true).drop 1, .end), { bytes := artifactBytes, pos := 1871, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_159_e_tail0 :
    instructionSequenceAt 580 false { bytes := artifactBytes, pos := 1868, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[159]!) true).drop 0, .end), { bytes := artifactBytes, pos := 1871, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_184_t_tail1 :
    instructionSequenceAt 554 true { bytes := artifactBytes, pos := 1922, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[184]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 1923, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_184_t_tail0 :
    instructionSequenceAt 555 true { bytes := artifactBytes, pos := 1920, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[184]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 1923, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_184_e_tail6 :
    instructionSequenceAt 549 false { bytes := artifactBytes, pos := 1941, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[184]!) true).drop 6, .end), { bytes := artifactBytes, pos := 1942, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_184_e_tail0 :
    instructionSequenceAt 555 false { bytes := artifactBytes, pos := 1923, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[184]!) true).drop 0, .end), { bytes := artifactBytes, pos := 1942, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_192_t_tail1 :
    instructionSequenceAt 546 true { bytes := artifactBytes, pos := 1957, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[192]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 1958, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_192_t_tail0 :
    instructionSequenceAt 547 true { bytes := artifactBytes, pos := 1956, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[192]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 1958, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_192_e_tail1 :
    instructionSequenceAt 546 false { bytes := artifactBytes, pos := 1960, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[192]!) true).drop 1, .end), { bytes := artifactBytes, pos := 1961, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_192_e_tail0 :
    instructionSequenceAt 547 false { bytes := artifactBytes, pos := 1958, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[192]!) true).drop 0, .end), { bytes := artifactBytes, pos := 1961, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_220_t_tail1 :
    instructionSequenceAt 518 true { bytes := artifactBytes, pos := 2015, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[220]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 2016, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_220_t_tail0 :
    instructionSequenceAt 519 true { bytes := artifactBytes, pos := 2013, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[220]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 2016, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_220_e_tail6 :
    instructionSequenceAt 513 false { bytes := artifactBytes, pos := 2034, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[220]!) true).drop 6, .end), { bytes := artifactBytes, pos := 2035, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_220_e_tail0 :
    instructionSequenceAt 519 false { bytes := artifactBytes, pos := 2016, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[220]!) true).drop 0, .end), { bytes := artifactBytes, pos := 2035, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_228_t_tail1 :
    instructionSequenceAt 510 true { bytes := artifactBytes, pos := 2050, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[228]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 2051, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_228_t_tail0 :
    instructionSequenceAt 511 true { bytes := artifactBytes, pos := 2049, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[228]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 2051, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_228_e_tail1 :
    instructionSequenceAt 510 false { bytes := artifactBytes, pos := 2053, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[228]!) true).drop 1, .end), { bytes := artifactBytes, pos := 2054, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_228_e_tail0 :
    instructionSequenceAt 511 false { bytes := artifactBytes, pos := 2051, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[228]!) true).drop 0, .end), { bytes := artifactBytes, pos := 2054, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_253_t_tail1 :
    instructionSequenceAt 485 true { bytes := artifactBytes, pos := 2105, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[253]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 2106, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_253_t_tail0 :
    instructionSequenceAt 486 true { bytes := artifactBytes, pos := 2103, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[253]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 2106, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_253_e_tail6 :
    instructionSequenceAt 480 false { bytes := artifactBytes, pos := 2124, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[253]!) true).drop 6, .end), { bytes := artifactBytes, pos := 2125, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_253_e_tail0 :
    instructionSequenceAt 486 false { bytes := artifactBytes, pos := 2106, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[253]!) true).drop 0, .end), { bytes := artifactBytes, pos := 2125, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_261_t_tail1 :
    instructionSequenceAt 477 true { bytes := artifactBytes, pos := 2140, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[261]!) false).drop 1, .otherwise), { bytes := artifactBytes, pos := 2141, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_261_t_tail0 :
    instructionSequenceAt 478 true { bytes := artifactBytes, pos := 2139, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[261]!) false).drop 0, .otherwise), { bytes := artifactBytes, pos := 2141, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_261_e_tail1 :
    instructionSequenceAt 477 false { bytes := artifactBytes, pos := 2143, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[261]!) true).drop 1, .end), { bytes := artifactBytes, pos := 2144, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_261_e_tail0 :
    instructionSequenceAt 478 false { bytes := artifactBytes, pos := 2141, limit := 2178 } =
      .ok (((Instr.childBody ((Cache.raw.codes[8]!.body)[261]!) true).drop 0, .end), { bytes := artifactBytes, pos := 2144, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail280 :
    instructionSequenceAt 461 false { bytes := artifactBytes, pos := 2177, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 280, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail272 :
    instructionSequenceAt 469 false { bytes := artifactBytes, pos := 2164, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 272, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail264 :
    instructionSequenceAt 477 false { bytes := artifactBytes, pos := 2148, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 264, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail256 :
    instructionSequenceAt 485 false { bytes := artifactBytes, pos := 2129, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 256, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail248 :
    instructionSequenceAt 493 false { bytes := artifactBytes, pos := 2092, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 248, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail240 :
    instructionSequenceAt 501 false { bytes := artifactBytes, pos := 2075, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 240, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail232 :
    instructionSequenceAt 509 false { bytes := artifactBytes, pos := 2060, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 232, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail224 :
    instructionSequenceAt 517 false { bytes := artifactBytes, pos := 2041, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 224, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail216 :
    instructionSequenceAt 525 false { bytes := artifactBytes, pos := 2004, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 216, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail208 :
    instructionSequenceAt 533 false { bytes := artifactBytes, pos := 1988, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 208, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail200 :
    instructionSequenceAt 541 false { bytes := artifactBytes, pos := 1975, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 200, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail192 :
    instructionSequenceAt 549 false { bytes := artifactBytes, pos := 1954, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 192, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail184 :
    instructionSequenceAt 557 false { bytes := artifactBytes, pos := 1918, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 184, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail176 :
    instructionSequenceAt 565 false { bytes := artifactBytes, pos := 1903, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 176, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail168 :
    instructionSequenceAt 573 false { bytes := artifactBytes, pos := 1887, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 168, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail160 :
    instructionSequenceAt 581 false { bytes := artifactBytes, pos := 1871, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 160, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail152 :
    instructionSequenceAt 589 false { bytes := artifactBytes, pos := 1852, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 152, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail144 :
    instructionSequenceAt 597 false { bytes := artifactBytes, pos := 1815, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 144, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail136 :
    instructionSequenceAt 605 false { bytes := artifactBytes, pos := 1800, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 136, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail128 :
    instructionSequenceAt 613 false { bytes := artifactBytes, pos := 1786, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 128, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail120 :
    instructionSequenceAt 621 false { bytes := artifactBytes, pos := 1766, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 120, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail112 :
    instructionSequenceAt 629 false { bytes := artifactBytes, pos := 1730, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 112, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail104 :
    instructionSequenceAt 637 false { bytes := artifactBytes, pos := 1713, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 104, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail96 :
    instructionSequenceAt 645 false { bytes := artifactBytes, pos := 1698, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 96, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail88 :
    instructionSequenceAt 653 false { bytes := artifactBytes, pos := 1678, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 88, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail80 :
    instructionSequenceAt 661 false { bytes := artifactBytes, pos := 1642, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 80, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail72 :
    instructionSequenceAt 669 false { bytes := artifactBytes, pos := 1626, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 72, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail64 :
    instructionSequenceAt 677 false { bytes := artifactBytes, pos := 1613, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 64, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail56 :
    instructionSequenceAt 685 false { bytes := artifactBytes, pos := 1597, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 56, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail48 :
    instructionSequenceAt 693 false { bytes := artifactBytes, pos := 1578, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 48, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail40 :
    instructionSequenceAt 701 false { bytes := artifactBytes, pos := 1541, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 40, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail32 :
    instructionSequenceAt 709 false { bytes := artifactBytes, pos := 1525, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 32, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail24 :
    instructionSequenceAt 717 false { bytes := artifactBytes, pos := 1509, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 24, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail16 :
    instructionSequenceAt 725 false { bytes := artifactBytes, pos := 1490, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 16, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail8 :
    instructionSequenceAt 733 false { bytes := artifactBytes, pos := 1453, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 8, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

@[cbv_eval] theorem sequence8_tail0 :
    instructionSequenceAt 741 false { bytes := artifactBytes, pos := 1437, limit := 2178 } =
      .ok (((Cache.raw.codes[8]!.body).drop 0, .end), { bytes := artifactBytes, pos := 2178, limit := 2178 }) := by cbv

theorem code8_decoded_parts :
    code { bytes := artifactBytes, pos := 1432, limit := 16006 } = .ok (Cache.raw.codes[8]!, { bytes := artifactBytes, pos := 2178, limit := 16006 }) := by
  refine code_eq_of_parts (size := 744)
    (payload := { bytes := artifactBytes, pos := 1434, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 1437, limit := 2178 })
    (bodyFinish := { bytes := artifactBytes, pos := 2178, limit := 2178 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence8_tail0
  · rfl

#print axioms code8_decoded_parts
end Project.TinyGpt2Hidden.Artifact
