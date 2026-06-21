import Erdos176Lean.SmallKCommon

/-!
# Erdős problem 176: `k = 4` finite appendix
-/

namespace Erdos176Lean
namespace SmallK

theorem exactAtCode_four_thirteen :
    exactAtCode 4 13 = true := by
  native_decide

theorem goodCode_four_thirteen :
    goodCode 4 13 = true := by
  native_decide

theorem allBeforeFalse_four_thirteen :
    allBeforeFalse 4 13 = true := by
  native_decide

end SmallK
end Erdos176Lean
