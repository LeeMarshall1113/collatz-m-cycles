import Collatz.MCycle109Certs12

/-!
# Certificates of the listed shapes of `data109`, chunks 48..51
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_48 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_48 = true := by
  decide +kernel

theorem certs109_49 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_49 = true := by
  decide +kernel

theorem certs109_50 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_50 = true := by
  decide +kernel

theorem certs109_51 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_51 = true := by
  decide +kernel

end Collatz
