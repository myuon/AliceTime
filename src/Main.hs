{-# LANGUAGE DeriveFunctor, Rank2Types, TypeOperators, DataKinds #-}
import Haste
import Haste.DOM
import Haste.Events
import Haste.Foreign
import Control.Monad.State
import Data.List
import Data.Time
import Data.IORef
import qualified Data.Map as M
import Lens.Family2
import Lens.Family2.Unchecked (lens)
import Lens.Family2.State.Lazy
import MakeLense

setHTML :: MonadIO m => Elem -> String -> m ()
setHTML el t = setProp el "innerHTML" t

addHTML :: MonadIO m => Elem -> String -> m ()
addHTML el t = do
  t0 <- getProp el "innerHTML"
  setProp el "innerHTML" (t0 ++ t)

removeAttr :: (MonadIO m) => Elem -> String -> m ()
removeAttr e c = liftIO $ rmc e c
  where
    {-# NOINLINE rmc #-}
    rmc :: Elem -> String -> IO ()
    rmc = ffi $ toJSString "(function(e,c){e.removeAttribute(c);})"

onceStateT :: (MonadIO m) => IORef a -> StateT a IO r -> m r
onceStateT ref m = liftIO $ do
  x <- readIORef ref
  (a,x') <- runStateT m x
  writeIORef ref $! x'
  return a

ix :: (Ord k) => k -> Lens' (M.Map k a) a
ix n = lens (M.! n) (\l x -> M.insert n x l)

data Date = M | T | W | F | S deriving (Eq, Ord, Enum, Show)
type Month = (Int, Date)

nextDate :: Date -> Date
nextDate d
  | d == S = M
  | otherwise = toEnum $ 1 + fromEnum d

chunksOf :: Int -> [a] -> [[a]]
chunksOf n [] = []
chunksOf n xs = take n xs : chunksOf n (drop n xs)

calendarHTML :: Month -> String
calendarHTML (n, d) = concat $ concat $ fmap (\x -> ["<tr>"] ++ x ++ ["</tr>"]) $ fmap (fmap (\x -> "<td>" ++ x ++ "</td>")) $ fmap (fmap (\x -> if x == 0 then "" else show x)) weeks where
  weeks = chunksOf (length [M .. S]) $ go 1 M (d == M)
  go i date b
    | i > n = replicate (fromEnum S - fromEnum date + 1) 0
    | b == True = i : go (i + 1) (nextDate date) b
    | otherwise = 0 : go i (nextDate date) (d == nextDate date)

data Working' a = None | Collecting a deriving (Show, Functor)
type Working = Working' NominalDiffTime

type Game = UnionT '[
  "time" :< UTCTime,
  "timeDelta" :< NominalDiffTime,
  "working" :< Working,
  "items" :< M.Map String Int,
  "counter" :< Int
  ]

time :: Lens' Game UTCTime; time = lenses (Name :: Name "time")
timeDelta :: Lens' Game NominalDiffTime; timeDelta = lenses (Name :: Name "timeDelta")
working :: Lens' Game Working; working = lenses (Name :: Name "working")
items :: Lens' Game (M.Map String Int); items = lenses (Name :: Name "items")
counter :: Lens' Game Int; counter = lenses (Name :: Name "counter")

shopItems :: M.Map String (UnionT '["name" :< String, "price" :< Int])
shopItems = M.fromList $ [
  ("sandwich", build "サンドウィッチ" 200),
  ("pickaxe", build "ピッケル" 1000),
  ("basket", build "バスケット" 1500)
  ]
  where
    build name price =
      sinsert (Tag name :: "name" :< String) $
      sinsert (Tag 200 :: price :< Int) $
      Union HNil

itemBagList :: [String]
itemBagList = ["money", "wood", "pickaxe", "basket", "sandwich"]

itemDisplayLabel :: String -> Int -> (String, String)
itemDisplayLabel "wood" n = ("木材", show n ++ " 本")
itemDisplayLabel "money" n = ("所持金", show n ++ " G")
itemDisplayLabel "sandwich" n = ("サンドウィッチ", show n ++ " 個")
itemDisplayLabel "pickaxe" n = ("ピッケル", "")
itemDisplayLabel "basket" n = ("バスケット", "")

workingAction :: Working -> StateT Game IO ()
workingAction None = return ()
workingAction (Collecting _) = do
  c <- use counter
  when (c `mod` 10 == 0) $ do
    items . ix "wood" += 1

main = do
  t <- getCurrentTime
  ref <- newIORef $ check $
    sinsert (Tag t :: "time" :< UTCTime) $
    sinsert (Tag 100 :: "timeDelta" :< NominalDiffTime) $
    sinsert (Tag None :: "working" :< Working) $
    sinsert (Tag (M.fromList [("money", 1000), ("wood", 0)]) :: "items" :< M.Map String Int) $
    sinsert (Tag 0 :: "counter" :< Int) $
    Union HNil

  withElem "calendar" $ \e -> do
    let m = (20, W)
    setHTML e $ calendarHTML m

  withElem "outskirts-time" $ \e -> do
    onEvent e Click $ \_ -> do
      onceStateT ref $ do
        timeDelta += 30

  withElem "forest-collecting" $ \e -> do
    onEvent e Click $ \_ -> do
      setAttr e "disabled" "disabled"
      onceStateT ref $ do
        working .= Collecting 0

  withElem "shop" $ \e -> do
    forM_ (M.assocs shopItems) $ \(itemID, item) -> do
      eitem <- newElem "button" `with` [
        attr "type" =: "button",
        attr "class" =: "btn btn-default"]

      appendChild e eitem
      setHTML eitem $ item ^. lenses (Name :: Name "name") ++ "(-" ++ show (item ^. lenses (Name :: Name "price")) ++ ")"

      onEvent eitem Click $ \_ -> do
        setAttr eitem "disabled" "disabled"

        onceStateT ref $ do
          its <- use items
          case M.member itemID its of
            True -> items . ix itemID += 1
            False -> items . ix itemID .= 1

  setTimer (Repeat 100) $ do
    onceStateT ref $ do
      counter += 1

      dt <- use timeDelta
      time %= addUTCTime (dt / 1000)

      working %= fmap (+ dt / 1000)
      workingAction =<< use working

      w <- use working
      case w of
        None -> return ()
        Collecting t -> when (t >= 5) $ do
          liftIO $ withElem "forest-collecting" $ \e -> do
            removeAttr e "disabled"

          working .= None

      t <- use time
      withElem "clock-time" $ \e -> do
        setHTML e $ formatTime defaultTimeLocale "%H:%M:%S" t

      withElem "alice-status-table" $ \e -> do
        setHTML e $ ""

        its <- use items
        forM_ itemBagList $ \k -> do
          when (M.member k its) $ do
            let (th,td) = itemDisplayLabel k (its ^. ix k)
            addHTML e $ "<tr><th>" ++ th ++ "</th><td>" ++ td ++ "</td></tr>"

-- 街外れの魔女
-- 時間をお金のmultiplierにかえてくれる？
-- →時間の進みが加速する
