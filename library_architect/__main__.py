"""Entry point for `python -m library_architect`."""

from dotenv import load_dotenv

load_dotenv()

from library_architect.cli import main

if __name__ == "__main__":
    main()
