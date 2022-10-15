# Left-right Concurrency With Thread ID Based Epochs

Consider a "left-right" data structure where all readers read from one copy of
the data structure, call this A, while a single writer writes modifies the
second copy, call this B. Then to enact or flush the changes made by the writer
simply switch all readers to read from copy B. Now comes a tricky bit, how do
you know when all the readers are done reading from copy A and allow the writer
to write to it? The basic idea if fairly simple; keep track of when readers are
reading. This can be done using "epochs".

For each reader keep a counter. When the counter is even, the reader is
currently not reading from the data structure. When the reader starts to read
from the data structure increment the counter by one, making it odd. Once the
reader is done reading increment the counter again by one, making it even again.
This allows us to determine when a reader is actually reading from the data
structure, because the "epoch" will be odd.

Various implementation exist of this. For Rust the most well known one is the
[`left_right`] crate by [Jon Gjengset] and this crate own a lot of it's design
to that crate. Similarly the hashmap implementation is similar to the [`evmap`]
crate based on `left_right`, also by Jon Gjengset.

[`left_right`]: https://crates.io/crates/left-right
[Jon Gjengset]: https://github.com/jonhoo
[`evmap`]: https://crates.io/crates/evmap
