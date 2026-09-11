class Infera < Formula
  desc "Prolog-inspired logic language with sorts, modes, tabling and CLP(Z)"
  homepage "https://github.com/hyperswine/NeoProlog"
  url "https://github.com/hyperswine/NeoProlog.git",
      tag: "v2.0.0"
  license "GPL-3.0-only"
  head "https://github.com/hyperswine/NeoProlog.git", branch: "main"

  depends_on "cabal-install" => :build
  depends_on "ghc" => :build

  def install
    system "cabal", "v2-update"
    system "cabal", "v2-install", *std_cabal_v2_args
    doc.install "README.md"
    pkgshare.install "examples"
  end

  test do
    (testpath/"hello.nprolog").write <<~PROLOG
      greet world.
      double : det (int: <=) (int: =>).
      double X Y <- Y is X * 2.
      > greet X?
      > double 21 Y?
    PROLOG
    output = pipe_output("#{bin}/infera #{testpath}/hello.nprolog", ":q\n")
    assert_match "X = world", output
    assert_match "Y = 42", output
  end
end
