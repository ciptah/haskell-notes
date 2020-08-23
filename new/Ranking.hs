module Ranking
  ( Document
  , TrainingDoc(TD)
  )
where

import Sets
import Vectors

-- Definitions in Section 3.1
-- `d` is the size of the feature vector.
type Document d = RD n
data TrainingDoc d = TD (Document n) RealNum
data TrainingQuery d = Q [TrainingDoc d]
type TrainingSet d = [TrainingQuery]
