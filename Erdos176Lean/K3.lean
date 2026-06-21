import Erdos176Lean.SmallKCommon

/-!
# Erdős problem 176: `k = 3` finite appendix
-/

namespace Erdos176Lean
namespace SmallK

theorem exactAtCode_three_nine :
    exactAtCode 3 9 = true := by
  native_decide

theorem goodCode_three_nine :
    goodCode 3 9 = true := by
  native_decide

theorem allBeforeFalse_three_nine :
    allBeforeFalse 3 9 = true := by
  native_decide

end SmallK
end Erdos176Lean
