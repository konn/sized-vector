{-# LANGUAGE QuasiQuotes #-}
module Main where
import           Control.DeepSeq
import           Control.Parallel.Strategies
import           Criterion
import           Data.Type.Natural
import qualified Data.Vector.Sized           as V
import           Progression.Main
import           System.Environment

main :: IO ()
main = do
  name : rest <- getArgs
  v10 <- return $!! ((V.replicate [snat|10|] ()) `using` rdeepseq)
  v100 <- return $!! ((V.replicate [snat|100|] ()) `using` rdeepseq)
  v200 <- return $!! ((V.replicate [snat|200|] ()) `using` rdeepseq)
  withArgs (("-n"++name) : rest) $
    defaultMain $
    bgroup "bench" [ bgroup "reverse"
                     [ bench "10" $ nf V.reverse v10
                     , bench "100" $ nf V.reverse v100
                     , bench "1000" $ nf V.reverse v200
                     ]
                   , bgroup "intersperse"
                     [ bench "10" $ nf (V.intersperse ()) v10
                     , bench "100" $ nf (V.intersperse ()) v100
                     , bench "200" $ nf (V.intersperse ()) v200
                     ]
                   ]
