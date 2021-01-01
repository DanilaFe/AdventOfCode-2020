# Advent of Code 2020 Solutions
Here's to my first 50 star year since 2017! The goal
was to make it to top 100 at least once this year,
and it finally came true on day 22 (and again in day 25
part 2, but that hardly counts). Honestly,
I am not at all happy with myself, though.

## Kinds of Solutions
I "raced" in [Crystal](https://crystal-lang.org), but also tried my hand at
formal verification in [Coq](https://coq.inria.fr/), and tried out
an APL dialect called [J](https://jsoftware.com/) for fun.
I didn't always clean my race day solutions, particularly the ones to the
"hard" days. I will write about my Coq solutions on [my site](https://danilafe.com).

## Rankings
Here's the (rather embarassing) table with my times.
```
      -------Part 1--------   -------Part 2--------
Day       Time  Rank  Score       Time  Rank  Score
 25   00:07:18   105      0   00:07:24    94      7
 24   00:25:27  1496      0   00:43:46  1165      0
 23   00:27:30   887      0   01:35:00  1057      0
 22   00:03:44    42     59   01:16:52  2242      0
 21   00:21:57   612      0   00:26:05   439      0
 20   00:27:52   465      0   03:00:50   845      0
 19   00:14:56   123      0   00:48:50   439      0
 18   00:26:17  1209      0   00:28:01   574      0
 17   00:17:23   400      0   00:19:14   281      0
 16   00:11:50   627      0   01:03:40  2040      0
 15   00:18:11  1772      0   00:30:38  1924      0
 14   00:18:05  1220      0   00:39:57  1173      0
 13   00:04:59   198      0   01:05:11  1606      0
 12   00:06:19   206      0   00:14:17   245      0
 11   00:13:23   414      0   00:19:11   261      0
 10   00:05:04   293      0   00:31:04  1493      0
  9   00:08:55  1721      0   00:26:50  3540      0
  8   00:04:23   275      0   00:09:56   256      0
  7   00:17:46   832      0   00:24:22   615      0
  6   00:03:31   385      0   00:09:38   999      0
  5   00:08:21   839      0   00:27:23  3404      0
  4   00:07:40   786      0   00:20:26   440      0
  3   00:02:46   119      0   00:07:40   448      0
  2   00:03:48   341      0   00:06:01   272      0
  1   00:07:52  1072      0   00:09:00   748      0
  ```

## Crystal for Competitive Programming
I really enjoyed writing Crystal for the Advent of Code, but there were a few reasons
why it wasn't perfect for the task.

* When you're not banking on brute force speed, you lose some time to the compiler.
* Numbers are _always_ 32-bit by default, and require constant `_i64` suffixes everywhere
in the code when they're involved.
* Type annotations (however necessary they are) for hashes and arrays make refactoring
a little bit slower.
