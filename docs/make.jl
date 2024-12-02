using Documenter, Dice

const pages = [
    "Home" => "index.md"
]
makedocs(
    sitename="Alea.jl",
    pages=pages
)
