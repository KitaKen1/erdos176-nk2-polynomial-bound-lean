import Erdos176Lean.SmallKCommon

/-!
# Erdős problem 176: `k = 2` finite appendix
-/

namespace Erdos176Lean
namespace SmallK

theorem exactAtCode_two_three :
    exactAtCode 2 3 = true := by
  native_decide

theorem goodCode_two_three :
    goodCode 2 3 = true := by
  native_decide

theorem allBeforeFalse_two_three :
    allBeforeFalse 2 3 = true := by
  native_decide

end SmallK
end Erdos176Lean
