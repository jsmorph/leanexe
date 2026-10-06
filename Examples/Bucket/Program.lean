namespace Examples.Bucket

/-- The index of the histogram bucket of width `width` starting at `lo` that
holds `x`.  Values below `lo` and NaN fall in bucket 0, and values beyond the
last word clamp to `2^64 - 1`. -/
def bucket (x lo width : Float) : UInt64 := ((x - lo) / width).toUInt64

end Examples.Bucket
