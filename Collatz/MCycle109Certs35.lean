import Collatz.MCycle109Certs34

/-!
# Certificates of the listed shapes of `data109`, chunks 136..139
-/

set_option Elab.async false
set_option maxRecDepth 100000

namespace Collatz

theorem certs109_136 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_136 = true := by
  decide +kernel

theorem certs109_137 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_137 = true := by
  decide +kernel

theorem certs109_138 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_138 = true := by
  decide +kernel

theorem certs109_139 : certsOK3 109 20 grid109 grid3_107 data109.certs shapes109_139 = true := by
  decide +kernel

end Collatz
