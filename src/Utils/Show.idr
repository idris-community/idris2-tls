module Utils.Show

import Data.List

export
show_record : String -> List (String, String) -> String
show_record adt_name fields = adt_name <+> " { " <+> (concat $ intersperse "; " $ map (\(a,b) => a <+> " = " <+> b) $ fields) <+> " }"
