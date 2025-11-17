                                 2   2   2   2   2
HashTable{AOTideal => ideal (0, y , y , y , y , y )                            }
                                 1   2   3   4   5
                                2   2   2   2   2
          AOTinIdeal => ideal (y , y , y , y , y )
                                5   4   3   2   1
          graph => {set {0, 6}, set {1, 6}, set {2, 6}, set {3, 6}, set {4, 6}}
                                 2      3     4    5
          hSeries => 1 + 5T + 10T  + 10T  + 5T  + T
          hyperplanes => {a - g, b - g, c - g, d - g, e - g}
          numVariables => 5
          WLPfull => "The AOT algebra has WLP"
          WLPin => "The AOT algebra has WLP"


R = QQ[y_1..y_5]
AOTideal = ideal map(R^1,R^{{0}, {-2}, {-2}, {-2}, {-2}, {-2}},{{0, y_1^2, y_2^2, y_3^2, y_4^2, y_5^2}})
AOTinIdeal = ideal map(R^1,R^{{-2}, {-2}, {-2}, {-2}, {-2}},{{y_5^2, y_4^2, y_3^2, y_2^2, y_1^2}})
G = graph {set {0, 6}, set {1, 6}, set {2, 6}, set {3, 6}, set {4, 6}}
