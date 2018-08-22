import Data.List
  
data Box = Hole | Possibilities [Int] | Sol Int

instance Show Box where
  show Hole = show "x"
  show (Possibilities a) = show a
  show (Sol a) = show a

type Puzzle = [[Box]]
type Row = [Box]
type Column = [Box]
type Location = (Int, Int)

puzzle :: Puzzle
puzzle = [[Sol 5, Hole, Hole, Sol 7, Hole, Hole, Hole, Hole, Hole],
          [Hole, Sol 4, Hole, Hole, Hole, Hole, Sol 6, Sol 8, Hole],
          [Hole, Hole, Sol 3, Hole, Sol 2, Sol 6, Hole, Hole, Hole],
          [Hole, Hole, Sol 2, Hole, Hole, Sol 5, Hole, Hole, Hole],
          [Hole, Sol 8, Hole, Hole, Sol 3, Hole, Hole, Hole, Hole],
          [Hole, Hole, Sol 1, Hole, Sol 8, Hole, Hole, Sol 4, Sol 5],
          [Hole, Hole, Hole, Hole, Hole, Hole, Sol 9, Hole, Hole],
          [Sol 6, Hole, Hole, Sol 5, Hole, Sol 3, Sol 2, Hole, Hole],
          [Hole, Hole, Hole, Sol 9, Sol 6, Hole, Sol 3, Sol 1, Hole]]
          
getSolutionsInBox :: Box -> Int
getSolutionsInBox (Sol a) = a
getSolutionsInBox (Hole) = 0
getSolutionsInBox (Possibilities a) = 0

getPossInBox :: Box -> [Int]
getPossInBox (Sol a) = [a]
getPossInBox (Hole) = [1..9]
getPossInBox (Possibilities a) = a

makePossFromUniqueConstraintList :: [Int] -> Box
makePossFromUniqueConstraintList [] = Possibilities [1..9]
makePossFromUniqueConstraintList a = Possibilities ([1..9] \\ a)

replaceBoxWithAnother :: Box -> Box -> Box
replaceBoxWithAnother (Sol a) _ = (Sol a)
replaceBoxWithAnother _ (Sol a) = (Sol a)
replaceBoxWithAnother a Hole = a
replaceBoxWithAnother (Possibilities a) (Possibilities b) =
  let len = length a
  in  if (len == 1) then Sol (a !! 0)
      else let x = a `intersect` b
           in  if (length x == 1) then Sol (x !! 0)
               else Possibilities x
  
getLeft :: [Box] -> [Box]
getLeft list = 
  let (l, _) = splitAt 3 list
  in  l

getCenter :: [Box] -> [Box]
getCenter list = 
  let (_, c) = splitAt 3 list
      (center, _) = splitAt 3 c
  in  center
  
getRight :: [Box] -> [Box]
getRight list = 
  let (_, c) = splitAt 3 list
      (_, right) = splitAt 3 c
  in  right
  
updatePossUsingOtherPoss :: [Box] -> Box -> Box
updatePossUsingOtherPoss boxes (Possibilities a) =
  let posses = concat $ map getPossInBox boxes
      b = a \\ posses
  in  if (length b) == 1 then Sol (b !! 0)
      else Possibilities a
updatePossUsingOtherPoss _ Hole = Hole
updatePossUsingOtherPoss _ (Sol a) = Sol a

updateUsingNeighbors :: Location -> Puzzle -> Puzzle
updateUsingNeighbors loc@(x, y) puz = 
  let h = quot x 3
      v = quot y 3
      (top, rest) = splitAt 3 puz
      (middle, bottom) = splitAt 3 rest
      stack = case v of 0 -> top
                        1 -> middle
                        2 -> bottom
      sliceGetter = case h of 0 -> getLeft
                              1 -> getCenter
                              2 -> getRight
      a = mod x 3
      b = mod y 3
      z = b*3 + a
      (rowsBefore, _:rowsAfter) = splitAt y puz
      (rBefore, rAt:rAfter) = splitAt x (puz !! y)
      (cBefore, cAt:cAfter) = splitAt y ((transpose puz) !! x)
      (qBefore, qAt:qAfter) = splitAt z (concat (map sliceGetter stack))
      rowPosses = rBefore ++ rAfter
      columnPosses = cBefore ++ cAfter
      boxPosses = qBefore ++ qAfter
      newBox = updatePossUsingOtherPoss rowPosses (updatePossUsingOtherPoss columnPosses (updatePossUsingOtherPoss boxPosses cAt))
  in  (rowsBefore ++ (rBefore ++ (newBox:rAfter)):rowsAfter)

updateRowConstraints :: Puzzle -> Puzzle
updateRowConstraints puz =
  let getPoss = Possibilities . (\row -> [1..9] \\ (map getSolutionsInBox row))
      newRow = (\row -> map (replaceBoxWithAnother (getPoss row)) row)
  in  map newRow puz
  
updateColumnConstraints :: Puzzle -> Puzzle
updateColumnConstraints puz = transpose $ updateRowConstraints (transpose puz)

updateBoxConstraints :: Puzzle -> Puzzle
updateBoxConstraints puz = 
  let (top, rest) = splitAt 3 puz
      (middle, bottom) = splitAt 3 rest
      getConstraint = (\listOfLists sectioner -> Possibilities ([1..9] \\ (map getSolutionsInBox (concat (map sectioner listOfLists)))))
      getConstraints = (\listOfLists -> (getConstraint listOfLists getLeft):(getConstraint listOfLists getCenter):(getConstraint listOfLists getRight):[])
      topPoss = getConstraints top
      middlePoss = getConstraints middle
      bottomPoss = getConstraints bottom
      updateSection = (\poss row -> map (replaceBoxWithAnother poss) row)
      updateRow = (\posses row -> concat ((updateSection (posses !! 0) (getLeft row)):(updateSection (posses !! 1) (getCenter row)):(updateSection (posses !! 2) (getRight row)):[]))
      newTop = map (updateRow topPoss) top
      newMiddle = map (updateRow middlePoss) middle
      newBottom = map (updateRow bottomPoss) bottom
  in  concat (newTop:newMiddle:newBottom:[])

updateSectionWithUniqueConstraints :: [Row] -> [Row]
updateSectionWithUniqueConstraints stackedRows =
  let left = map getLeft stackedRows
      center = map getCenter stackedRows
      right = map getRight stackedRows
      unioner = (\list -> foldl (\acc poss -> acc `union` poss) [] (map getPossInBox list))
      l = updateListsWithDifferences $ map unioner left
      c = updateListsWithDifferences $ map unioner center
      r = updateListsWithDifferences $ map unioner right
      lPosses = map makePossFromUniqueConstraintList l
      cPosses = map makePossFromUniqueConstraintList c
      rPosses = map makePossFromUniqueConstraintList r
      rowUpdater = (\row poss -> map (replaceBoxWithAnother poss) row)
      lUpdated = zipWith (++) left (zipWith rowUpdater (zipWith (++) center right) lPosses)
      rUpdated = zipWith (++) (zipWith rowUpdater (zipWith (++) (map getLeft lUpdated) (map getCenter lUpdated)) rPosses) (map getRight lUpdated)
      customAddList = (\a b c -> a ++ b ++ c)
      cUpdated = zipWith3 customAddList (zipWith rowUpdater (map getLeft rUpdated) cPosses) (map getCenter rUpdated) (zipWith rowUpdater (map getRight rUpdated) cPosses)
  in  cUpdated
      
updateListsWithDifferences :: [[Int]] -> [[Int]]
updateListsWithDifferences listOfLists = 
  let a = listOfLists !! 0
      b = listOfLists !! 1
      c = listOfLists !! 2
      (x,y,z) = (((a \\ b) \\ c), ((b \\ a) \\ c), ((c \\ a) \\ b))
  in  x:y:z:[]
      
updateSpecialBoxConstraints :: Puzzle -> Puzzle
updateSpecialBoxConstraints puz = 
  let readyPuzzle = updateBoxConstraints puz
      (top, rest) = splitAt 3 readyPuzzle
      (middle, bottom) = splitAt 3 rest
      newTop = updateSectionWithUniqueConstraints top
      newMiddle = updateSectionWithUniqueConstraints middle
      newBottom = updateSectionWithUniqueConstraints bottom
  in  concat (newTop:newMiddle:newBottom:[])

boxAlreadySolved :: Box -> Bool
boxAlreadySolved (Sol a) = True
boxAlreadySolved _ = False

isSol :: Box -> Bool
isSol (Sol a) = True
isSol _ = False

isPuzzleSolved :: Puzzle -> Bool
isPuzzleSolved puz = all isSol $ concat puz 

solve :: Puzzle -> Puzzle
solve puz = 
  if (isPuzzleSolved puz) then puz
  else (let puzzStep = updateRowConstraints . updateColumnConstraints . updateSpecialBoxConstraints $ puz
            puzzStep2 = transpose (updateSpecialBoxConstraints (transpose puzzStep))
            puzzStep3 = foldr updateUsingNeighbors puzzStep2 [(x, y) | x <- [0..8], y <- [0..8]]
        in solve puzzStep3)

printRow :: Row -> IO()
printRow row = do
  flip mapM_ row $ \box -> putStr ((show box) ++ "|")
  putStrLn ""
  putStrLn "--------------------------------------------------------"

printPuzzle :: Puzzle -> IO()
printPuzzle puz = do
  flip mapM_ puz $ \row -> printRow row

main :: IO()
main = do
  printPuzzle puzzle
  putStrLn "Solving..."
  let solvedPuzzle = solve puzzle
  printPuzzle solvedPuzzle
  putStrLn "Done"