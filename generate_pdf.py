#!/usr/bin/env python3
"""
Generate PDF from ITC_Coq_Report.md

Usage:
  1. Install pandoc: brew install pandoc
  2. Run: python3 generate_pdf.py

  Or open ITC_Coq_Report.html in browser and print to PDF.
"""

import subprocess
import os
import sys

def check_pandoc():
    """Check if pandoc is available."""
    try:
        subprocess.run(['pandoc', '--version'], capture_output=True, check=True)
        return True
    except (subprocess.CalledProcessError, FileNotFoundError):
        return False

def generate_pdf_with_pandoc():
    """Generate PDF using pandoc."""
    cmd = [
        'pandoc',
        'ITC_Coq_Report.md',
        '-o', 'ITC_Coq_Report.pdf',
        '--toc',
        '--toc-depth=3',
        '-V', 'geometry:margin=1in',
        '-V', 'fontsize=11pt',
        '-V', 'documentclass=article',
        '--pdf-engine=xelatex'
    ]

    print("Generating PDF with pandoc...")
    try:
        subprocess.run(cmd, check=True)
        print("PDF generated successfully: ITC_Coq_Report.pdf")
        return True
    except subprocess.CalledProcessError as e:
        print(f"Error generating PDF: {e}")
        return False

def main():
    os.chdir(os.path.dirname(os.path.abspath(__file__)))

    if not os.path.exists('ITC_Coq_Report.md'):
        print("Error: ITC_Coq_Report.md not found")
        sys.exit(1)

    if check_pandoc():
        if generate_pdf_with_pandoc():
            sys.exit(0)

    print("\n" + "="*60)
    print("ALTERNATIVE: Open ITC_Coq_Report.html in a browser")
    print("and use File > Print > Save as PDF")
    print("="*60)

    if not check_pandoc():
        print("\nTo install pandoc:")
        print("  macOS: brew install pandoc")
        print("  Ubuntu: sudo apt-get install pandoc")
        print("  Windows: choco install pandoc")

if __name__ == '__main__':
    main()
