module Main

import Data.Vect

data FileSystem = DirTree String (List FileSystem) | FileTree String

pathFromVect : Vect n String -> String
pathFromVect xs = concat $ intersperse "/" $ reverse $ toList xs

linearize : (depth : List String) -> FileSystem -> List String
linearize depth (DirTree n []) = [concat $ reverse $ intersperse "/" (n :: depth)]
linearize depth (DirTree n files) = concatMap (linearize (n :: depth)) files
linearize depth (FileTree n) = [concat $ reverse $ intersperse "/" (n :: depth)]

Show FileSystem where
  show fs = concat $ intersperse "\n" $ linearize [] fs

||| Ls with accumulator, uses `dirEntry` to get to the next entry
lsAcc : Directory -> Maybe (List String) -> IO (Either FileError (List String))
lsAcc d files = do Right file <- dirEntry d
                     | Left err => pure (maybe
                                           (Left err) -- if we did not start collecting files, error
                                           (Right . filter notDot) -- else return the files we found
                                           files)
                   lsAcc d (Just (file :: (maybe [] id files)))
  where
    ||| Don't pay attention to files starting with a dot
    notDot : String -> Bool
    notDot "" = True
    notDot str = strHead str /= '.'

||| List all files in a directory
ls : String -> IO (Either FileError (List String))
ls name = do Right d <- dirOpen name | Left err => pure (Left err)
             result <- lsAcc d Nothing
             dirClose d
             pure result


||| like partition : (a -> Bool) -> List a -> (List a, List a) but in a monad
partitionM : Monad m => (a -> m Bool) -> List a -> m (List a, List a)
partitionM p [] = pure ([], [])
partitionM p (x :: xs) = do (yes, no) <- partitionM p xs
                            case !(p x) of
                                 True => pure (x :: yes, no)
                                 False => pure (yes, x :: no)

||| Traverse twice, once with function, once to flip applicatives around
doubleTraverse : Applicative n => Applicative m => Traversable l =>
                 (a -> m (n d)) -> l a -> m (n (l d))
doubleTraverse f x = traverse id <$> traverse f x

||| Construct a tree of all files in a directory structure
lsRec : Vect (S n) String -> IO (Either FileError FileSystem)
lsRec path@(directory :: ds) = do
    Right files <- ls (pathFromVect path) | Left err => pure (Left err)
    (dirs, files) <- partitionM (isDir path) files
    Right subTree <- doubleTraverse (\d => lsRec (d :: path)) dirs
      | Left err => pure (Left err)
    pure $ Right (DirTree directory (subTree ++ map FileTree files))
  where
    ||| Check if a path points to a directory. Couldn't find any other way
    isDir : Vect n String -> String -> IO Bool
    isDir arboresence name = do
      Right dir <- dirOpen (pathFromVect (name :: arboresence))
        | Left _ => pure False
      dirClose dir
      pure True

||| We don't care about the begining of the file path nor the file extension
||| The begining is the root folder, which will always be different
||| The filepath is `lidr` for idris1 and `idr` for Idris2 so it's not helpful
fixFormat : Nat -> String -> String
fixFormat n str = pack $ takeWhile (/= '.') $ drop n $ unpack str

missing : Eq a => List a -> List a -> List a
missing xs ys = filter (not . flip elem ys) xs

main : IO ()
main = do [_, folder1, folder2] <- getArgs
            | _ => putStrLn "Wrong arguments, expected two arguments"
          Right files1 <- lsRec [folder1] | _ => putStrLn ("could not list files in " ++ folder1)
          Right files2 <- lsRec [folder2] | _ => putStrLn ("could not list files in " ++ folder2)
          let linearFiles1 = map (fixFormat (length folder1)) $ linearize [] files1
          let linearFiles2 = map (fixFormat (length folder2)) $ linearize [] files2
          let missingFiles = missing linearFiles1 linearFiles2
          let percent = the Double (cast (length missingFiles)) / cast (length linearFiles1)
          putStrLn "missing: "
          putStrLn $ unlines missingFiles
          putStrLn $ "completion rate: " ++ show (abs (1 - percent))
          pure ()

